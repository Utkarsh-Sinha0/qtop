#!/usr/bin/env python

##################################################
##                     qtop                     ##
##################################################

##
## qtop is a tool to monitor queuing systems - https://github.com/qtop/qtop
##
## Copyright (c) 2016 Fotis Georgatos
## Copyright (c) 2016 Sotiris Fragkiskos
## Copyright (c) 2023 Hewlett Packard Enterprise Development LP
## Copyright (c) 2026 Jacob Hatchett
##
## SPDX-License-Identifier: MIT
##

import sys

from operator import itemgetter
from itertools import zip_longest, cycle
import subprocess
import select
import os
import re
import json
import datetime
from collections import namedtuple, OrderedDict, Counter
from os.path import realpath
from signal import signal, SIGPIPE, SIG_DFL
import termios
import contextlib
import glob
import tempfile
import logging
from ast import literal_eval
from qtop_py.constants import (
    SYSTEMCONFDIR,
    QTOPCONF_YAML,
    QTOP_LOGFILE,
    USERPATH,
    KEYPRESS_TIMEOUT,
    FALLBACK_TERMSIZE,
    SYMBOL_LONG_TAIL_USER,
    SYMBOL_UNKNOWN_NODE_STATE,
)
from qtop_py import fileutils
from qtop_py import utils
from qtop_py.plugins.demo import DemoBatchSystem
from qtop_py.plugins.oar import OARBatchSystem
from qtop_py.plugins.pbs import PBSBatchSystem
from qtop_py.plugins.sge import SGEBatchSystem
from qtop_py.plugins.slurm import SlurmBatchSystem
from math import ceil
from qtop_py.colormap import user_to_color_default, color_to_code, queue_to_color, nodestate_to_color_default
import qtop_py.yaml_parser as yaml
from qtop_py.ui.viewport import Viewport
from qtop_py.web import Web
from qtop_py import __version__
import time

here = sys.path[0]
PLUGIN_BATCH_SYSTEMS = (DemoBatchSystem, OARBatchSystem, PBSBatchSystem, SGEBatchSystem, SlurmBatchSystem)


def _configured_separator(config):
    separator = config.get("SEPARATOR", config.get("vertical_separator", "|"))
    return separator.replace("'", "") if isinstance(separator, str) else separator


def _reserved_user_symbols(config):
    return set(
        symbol
        for symbol in (
            config.get("non_existent_node_symbol", "#"),
            _configured_separator(config),
            "_",
            SYMBOL_LONG_TAIL_USER,
            SYMBOL_UNKNOWN_NODE_STATE,
        )
        if symbol
    )


def _available_possible_ids(config):
    reserved_symbols = _reserved_user_symbols(config)
    return [symbol for symbol in config["possible_ids"] if symbol not in reserved_symbols]


# TODO make the following work with py files instead of qtop.colormap files
# if not args.COLORFILE:
#     args.COLORFILE = os.path.expandvars('$HOME/qtop/qtop/qtop.colormap')


def compress_colored_line(s):
    ## TODO: black sheep
    t = [item for item in re.split(r"\x1b\[0;m", s) if item != ""]

    sts = []
    st = []
    colors = []
    prev_code = t[0][:-1]
    colors.append(prev_code)
    for idx, code_letter in enumerate(t):
        code, letter = code_letter[:-1], code_letter[-1]
        if prev_code == code:
            st.append(letter)
        else:
            sts.append(st)
            st = []
            st.append(letter)
            colors.append(code)
        prev_code = code
    sts.append(st)

    final_t = []
    for color, seq in zip(colors, sts):
        final_t.append(color + "".join(seq) + "\x1b[0;m")
    return "".join(final_t)


def literal_config_value(value):
    try:
        return literal_eval(value)
    except (ValueError, SyntaxError, TypeError):
        return value


def extract_regex_detail(regex, field):
    expression = (regex or "").strip()
    if not expression:
        return field.strip()

    match = re.match(r"^re\.search\((?P<quote>['\"])(?P<pattern>.*)(?P=quote),\s*field\)\.group\((?P<group>\d+)\)$", expression, re.DOTALL)
    if not match:
        raise ValueError("Unsupported user detail regex expression in %s" % QTOPCONF_YAML)

    found = re.search(match.group("pattern"), field)
    return found.group(int(match.group("group")))


def gauge_core_vectors(core_user_map, print_char_start, print_char_stop, coreline_notthere_or_unused, non_existent_symbol, remove_corelines):
    """
    generator that loops over each core user vector and yields a boolean stating whether the core vector can be omitted via
    REM_EMPTY_CORELINES or its respective switch
    """
    delta = print_char_stop - print_char_start
    for ind, k in enumerate(core_user_map.copy()):
        core_x_vector = core_user_map["Core" + str(ind) + "vector"][print_char_start:print_char_stop]
        core_x_str = "".join(str(x) for x in core_x_vector)
        yield core_x_vector, ind, k, coreline_notthere_or_unused(non_existent_symbol, remove_corelines, delta, core_x_str)


def get_date_obj_from_str(s, now):
    """
    Expects string s to be in either of the following formats:
    yyyymmddTHHMMSS, e.g. 20161118T182300
    HHMM, e.g. 1823 (current day is implied)
    mmddTHHMM, e.g. 1118T1823 (current year is implied)
    If it's in format #3, the the current year is assumed.
    If it's in format #2, either the current or the previous day is assumed,
    depending on whether the time provided is future or past.
    Optional ":/-" separators are also accepted between pretty much anywhere.
    returns a datetime object
    """
    s = "".join([x for x in s if x not in ":/-"])
    if "T" in s and len(s) == 15:
        inp_datetime = datetime.datetime.strptime(s, "%Y%m%dT%H%M%S")
    elif len(s) == 4:
        _inp_datetime = datetime.datetime.strptime(s, "%H%M")
        _inp_datetime = now.replace(hour=_inp_datetime.hour, minute=_inp_datetime.minute, second=0)
        inp_datetime = _inp_datetime if now > _inp_datetime else _inp_datetime.replace(day=_inp_datetime.day - 1)
    elif len(s) == 9:
        _inp_datetime = datetime.datetime.strptime(s, "%m%dT%H%M")
        inp_datetime = _inp_datetime.replace(year=now.year, second=0)
    else:
        logging.critical("The datetime format provided is incorrect.\nTry one of the formats: yyyymmddTHHMMSS, HHMM, mmddTHHMM.")
    return inp_datetime


@contextlib.contextmanager
def raw_mode(file):
    """
    Simple key listener implementation
    Taken from http://stackoverflow.com/questions/11918999/key-listeners-in-python/11919074#11919074
    Exits program with ^C or ^D
    """
    if args.ONLYSAVETOFILE:
        yield
    else:
        if args.WATCH:
            try:
                old_attrs = termios.tcgetattr(file.fileno())
            except:  # noqa: E722  ## FIXME, ruff complaint
                yield
            else:
                new_attrs = old_attrs[:]
                new_attrs[3] = new_attrs[3] & ~(termios.ECHO | termios.ICANON)
                try:
                    termios.tcsetattr(file.fileno(), termios.TCSADRAIN, new_attrs)
                    yield
                finally:
                    termios.tcsetattr(file.fileno(), termios.TCSADRAIN, old_attrs)
        else:
            yield


def load_yaml_config():
    """
    Loads ./QTOPCONF_YAML into a dictionary and then tries to update the dictionary
    with the same-named conf file found in:
    /env
    $HOME/.local/qtop/
    in that order.
    """
    # TODO: conversion to int should be handled internally in native yaml parser
    # TODO: fix_config_list should be handled internally in native yaml parser
    config = yaml.parse(os.path.join(realpath(QTOPPATH), QTOPCONF_YAML))
    logging.info("Default configuration dictionary loaded. Length: %s items" % len(config))

    try:
        config_env = yaml.parse(os.path.join(SYSTEMCONFDIR, QTOPCONF_YAML))
    except IOError:
        config_env = {}
        logging.info("%s could not be found in %s/" % (QTOPCONF_YAML, SYSTEMCONFDIR))
    else:
        logging.info("Env %s found in %s/" % (QTOPCONF_YAML, SYSTEMCONFDIR))
        logging.info("Env configuration dictionary loaded. Length: %s items" % len(config_env))

    try:
        config_user = yaml.parse(os.path.join(USERPATH, QTOPCONF_YAML))
    except IOError:
        config_user = {}
        logging.info("User %s could not be found in %s/" % (QTOPCONF_YAML, USERPATH))
    else:
        logging.info("User %s found in %s/" % (QTOPCONF_YAML, USERPATH))
        logging.info("User configuration dictionary loaded. Length: %s items" % len(config_user))

    config.update(config_env)
    config.update(config_user)

    if args.CONFFILE:
        try:
            config_user_custom = yaml.parse(os.path.join(USERPATH, args.CONFFILE))
        except IOError:
            try:
                config_user_custom = yaml.parse(os.path.join(CURPATH, args.CONFFILE))
            except IOError:
                config_user_custom = {}
                logging.info("Custom User %s could not be found in %s/ or current dir" % (args.CONFFILE, CURPATH))
            else:
                logging.info("Custom User %s found in %s/" % (QTOPCONF_YAML, CURPATH))
                logging.info("Custom User configuration dictionary loaded. Length: %s items" % len(config_user_custom))
        else:
            logging.info("Custom User %s found in %s/" % (QTOPCONF_YAML, USERPATH))
            logging.info("Custom User configuration dictionary loaded. Length: %s items" % len(config_user_custom))
        config.update(config_user_custom)

    logging.info("Updated main dictionary. Length: %s items" % len(config))
    fileutils.mkdir_p(os.path.expandvars(config["savepath"]))
    user_to_color = yaml.parse(os.path.join(QTOPPATH, config["user_color"].replace("'", "")))
    user_to_color_default.update(user_to_color)
    user_to_color = user_to_color_default
    nodestate_to_color = yaml.parse(os.path.join(QTOPPATH, config["nodestate_color"].replace("'", "")))
    nodestate_to_color_default.update(nodestate_to_color)
    nodestate_to_color = nodestate_to_color_default

    config["possible_ids"] = _available_possible_ids(config)

    return config, user_to_color, nodestate_to_color


def init_dirs(args, savepath):
    """
    Initialises and sets CURPATH, QTOPPATH
    Opens log file handler and closes stderr
    Creates savepath path if not existant
    """
    # log dir is created in init_logging()
    fileutils.mkdir_p(os.path.expandvars(savepath))
    # if there are command line OVERWRITES defined for log file then create the directory of that file
    if args.OPTION:
        for option in args.OPTION:
            if "logfile" in option:
                logfile_overwrite = os.path.expandvars(re.match(r"logfile=(.*)", option).group(1))
                fileutils.mkdir_p(os.path.dirname(logfile_overwrite))
    return args


def get_key_val_from_option_string(opt):
    """
    Get key, value by splitting in the 1st occurrence of '=' character.
    """
    try:
        key, val = opt.split("=", 1)
    except ValueError:
        logging.critical("Option %s is not in format key=val" % opt)
        sys.exit(1)
    return key, val


def update_config_with_cmdline_vars(args, config):
    config["rem_empty_corelines"] = int(config["rem_empty_corelines"])
    for opt in args.OPTION:
        key, val = get_key_val_from_option_string(opt)
        config[key] = literal_config_value(val)
    return config


def rem_empty_corelines(wn_occupancy, rem_empty_corelines):
    """
    if rem_empty_corelines is set to 1 or 2:
    """
    # TODO too much!!
    assert rem_empty_corelines in [0, 1, 2]
    try:
        transpose = args.TRANSPOSE
    except AttributeError:  # ugly, to be temporarily backwards compatible to tests (since function not in class)
        transpose = False
    if transpose:
        return wn_occupancy
    elif rem_empty_corelines == 0:
        return wn_occupancy
    elif rem_empty_corelines:
        # TODO use a function in Cluster here
        try:
            rem_empty_corelines - 1
        except TypeError:  # ugly, for config to change it to int
            rem_empty_corelines = int(rem_empty_corelines)
        max_height = len(wn_occupancy["Core0vector"])
        new_wn_occupancy = dict(wn_occupancy.copy())
        for core_nr in range(config["max_corelines"]):
            core_x_vector = wn_occupancy.get("Core" + str(core_nr) + "vector", ["" for _ in range(max_height)])
            core_x_str = "".join(str(x) for x in core_x_vector)
            if _coreline_notthere_or_unused(config["non_existent_node_symbol"], rem_empty_corelines, len(core_x_vector), core_x_str):
                for key in ("Core" + str(core_nr) + postfix for postfix in ("", "vector")):
                    new_wn_occupancy.pop(key, None)
        return new_wn_occupancy


def _coreline_notthere_or_unused(non_existent_symbol, remove_corelines, core_vector_len, core_str):
    non_existent_coreline = core_str == non_existent_symbol * core_vector_len
    if not non_existent_coreline:
        return False
    if remove_corelines == 1:
        return True
    if remove_corelines == 2:
        return True
    return False


def _resolve_syspath_command(command):
    try:
        return os.environ["QTOP_TEST_OVERRIDE_%s" % command.upper()]
    except KeyError:
        return os.path.join("/usr/bin", command)


def list_similar_schedulers(scheduler, schedulers):
    """
    Return scheduler names that are likely alternatives for a user typo.
    """
    return [known for known in schedulers if scheduler in known or known in scheduler]


def discover_qtop_batch_systems(batch_system_classes=PLUGIN_BATCH_SYSTEMS):
    """
    Return a mapping from scheduler name to batch system implementation class.
    """
    return {batch_system_class.scheduler_name: batch_system_class for batch_system_class in batch_system_classes}


def auto_get_avail_batch_system(config):
    """
    Get avail batchsystem automatically, based on which of the queuing system commands exist.
    """
    # TODO pbsnodes etc should not be hardcoded!
    for system, batch_command in config["signature_commands"].items():
        NOT_FOUND = subprocess.call([_resolve_syspath_command("which"), batch_command], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if not NOT_FOUND:
            if system != "demo":
                logging.debug("Auto-detected scheduler: %s" % system)
                return system

    else:
        raise SchedulerNotSpecified


def _sort_key(sort_by):
    if sort_by in (None, ""):
        return None
    if sort_by == "wn":
        return itemgetter("domainname")
    if sort_by == "state":
        return itemgetter("state")
    if sort_by == "np":
        return itemgetter("np")
    if sort_by == "seq_wn":
        return itemgetter("seq_wn")
    raise ValueError("Unsupported worker node sort key: %s" % sort_by)


class Cluster(object):
    """
    Contains WorkerNodes
    """

    def __init__(self, document, worker_nodes, WNFilter, config, args):
        self.worker_nodes = worker_nodes
        self.config = config
        self.args = args

    def _sort_worker_nodes(self):
        sort_by = self.config.get("sort_wn_by")
        sort_key = _sort_key(sort_by)
        if sort_key is None:
            return self.worker_nodes
        return sorted(self.worker_nodes, key=sort_key)

    def get_worker_nodes(self):
        return self.worker_nodes

    def _worker_name_from_regex(self, worker_node, name_key):
        domainname = worker_node["domainname"]
        node_regex = self.config.get(name_key)
        return extract_regex_detail(node_regex, domainname)

    def _node_is_down(self, worker_node):
        return "d" in worker_node["state"]

    def _node_is_offline(self, worker_node):
        return "o" in worker_node["state"]

    def _node_name_matches(self, node_filter, worker_node):
        host_key = "host" if self.args.FORCE_NAMES else "domainname"
        return worker_node[host_key] == node_filter

    def get_requested_wns(self, WNFilter):
        # Set of WNs that will be displayed. 2 cases:
        # 1. If -m is True we start by showing all WNs
        # 2. If -m is False we start by showing a WN if at least one core is used
        if self.args.NOMASKING:
            user_set = set()
            for wn in self.worker_nodes:
                user_set.update(wn["state"]["core_user_map"].keys())
            return [wn["domainname"] for wn in self.worker_nodes if set(wn["state"]["core_user_map"].keys()) != user_set]
        else:
            return [wn["domainname"] for wn in self.worker_nodes if any(x for x in wn["state"]["core_user_map"].values())]

    def filter_worker_nodes(self, user_input, WNFilter):
        """
        Choose the WNs to be shown. If the user has provided some input, filter the list of WNs according to user_input
        Else, return all the WNs
        """

        show_all = user_input in ("", None)
        if show_all:
            return self.worker_nodes, None, None, None, None

        offdown_nodes = []
        avail_nodes = []
        working_cores = []
        total_cores = []
        for x in user_input.split(","):
            if x.startswith("!"):
                node_filter = x[1:]
                offdown_nodes.append(node_filter)
            else:
                node_filter = x
            node_matches = [node for node in self.worker_nodes if self._node_name_matches(node_filter, node)]
            if not node_matches:
                logging.error(colorize("Selected node %s does not exist. Cancelling." % node_filter, "Red_L"))
                return self.worker_nodes, offdown_nodes, avail_nodes, working_cores, total_cores

            worker_node = node_matches[0]
            available = all(x == "_" for x in worker_node["state"]["core_user_map"].values())
            offline = self._node_is_offline(worker_node)
            down = self._node_is_down(worker_node)
            if x.startswith("!"):
                if available or not (offline or down):
                    working_cores.append(worker_node)
                    self.report_filtered_view()
                    continue
                logging.error(colorize("Selected node %s is not available. Cancelling." % node_filter, "Red_L"))
                return self.worker_nodes, offdown_nodes, avail_nodes, working_cores, total_cores
            elif down:
                logging.error(colorize("Selected node is down. Cancelling.", "Red_L"))
                return self.worker_nodes, offdown_nodes, avail_nodes, working_cores, total_cores
            elif offline:
                logging.error(colorize("Selected node is offline. Cancelling.", "Red_L"))
                return self.worker_nodes, offdown_nodes, avail_nodes, working_cores, total_cores
            elif not available:
                logging.error(colorize("Selected node is not available. Cancelling.", "Red_L"))
                return self.worker_nodes, offdown_nodes, avail_nodes, working_cores, total_cores
            else:
                avail_nodes.append(worker_node)
                self.report_filtered_view()

        return self.worker_nodes, offdown_nodes, avail_nodes, working_cores, total_cores

    @staticmethod
    @utils.CountCalls
    def report_filtered_view():
        logging.error("%s WN Occupancy view is filtered." % colorize("***", "Green_L"))


def keep_queue_initials_only_and_colorize(wnl, mapping):
    """
    Performs queue remapping and colorization of the output.
    """
    for wn in wnl:
        state = wn["state"]
        for core in state["core_job_map"]:
            try:
                qname = state["core_job_map"][core]["job_queue"]
            except (KeyError, TypeError):
                qname = "?"
            state["core_job_map"][core]["job_queue"] = qname[0].upper() if qname else "?"

            try:
                queue_color = mapping[qname]
            except KeyError:
                queue_color = mapping["queue_not_colored"]
            state["core_job_map"][core]["job_queue_color"] = queue_color
    return wnl


def colorize_nodestate(wnl, nodestate_to_color, colorize):
    """
    Replaces with colorized strings all states of nodes and the nonexistent node symbol
    """
    for node in wnl:
        node["state"]["state"] = colorize(node["state"].get("state", "?"), nodestate_to_color, node["state"].get("state", "?")[0])
        node["state"]["np"] = colorize(node["state"]["np"], "Cyan_L")
        node["state"]["core_user_map"] = {key: colorize(val) for key, val in node["state"]["core_user_map"].items()}
        for key, val in node["state"].items():
            if isinstance(val, list):
                node["state"][key] = colorize(val)
    return wnl


class WNFilter(object):
    filter_symbols = ":!"

    def __init__(self, config, WNFilter, cluster):
        self.cluster = cluster
        self.config = config
        self.WNFilter = WNFilter
        self._filter_list = []
        self.active_filter = None

    def update_active_filter(self, read_char):
        """
        Updates the active filter.
        Decides which of the filter sub-layers is active based on the WNFilter input line
        """
        if self.active_filter == "user_or_node":
            if read_char == "\x1b":
                self.active_filter = None
                return
            if read_char == "\x7f":
                try:
                    self._filter_list.pop()
                except IndexError:
                    return
            elif read_char == "\x15":  # ^U
                self._filter_list = []
            elif read_char in ("\x03", "\x04"):  # ^C or ^D
                raise KeyboardInterrupt
            elif read_char == "\r":
                self.active_filter = None
                return
            else:
                self._filter_list.append(read_char)
        elif read_char == "/":
            self.active_filter = "user_or_node"
        elif read_char in self.filter_symbols:
            self.active_filter = "node_state"
        else:
            self.active_filter = None

    def filter_worker_nodes(self, cluster):
        """
        Filter the nodes to be shown. If the user has provided a filter, filter the list of WNs according to it.
        Else, return all the WNs
        """

        user_input = "".join(self._filter_list)
        if self.active_filter != "user_or_node" and read_char == "\r":
            user_input += read_char
        return cluster.filter_worker_nodes(user_input, WNFilter)


def colorize(s, mapping=None, pattern=None):
    """
    INPUT: string, mapping e.g. user_to_color. ColorStr instance with color property, pattern matches any key in mapping.
    OUTPUT: string colored according to the mapping, with the best matching pattern.
    mapping can also be a string, e.g. 'Red_L'
    """
    try:
        if mapping is None:
            color = ""
        elif isinstance(mapping, str):
            color = color_to_code[mapping]
        else:
            color = mapping[pattern]
    except KeyError:
        color = ""

    if color:
        return "\x1b[0;%sm%s\x1b[0;m" % (color, s)
    return s


class WNOccupancy(object):
    """
    Creates Worker Node Objects
    """

    def __init__(self, cluster, config, document, user_to_color, job_ids):
        self.document = document
        self.config = config
        self.worker_nodes = cluster.get_worker_nodes()
        self.job_ids = job_ids
        self.account_jobs_table = []

    def _coreline_notthere_or_unused(self, non_existent_symbol, remove_corelines, core_vector_len, core_str):
        return _coreline_notthere_or_unused(non_existent_symbol, remove_corelines, core_vector_len, core_str)

    def _create_id_for_users(self, user_lot):
        """Updates user_id and id_info"""
        user_to_id = {}
        nr_users = len(user_lot)
        user_symbols = self.config["possible_ids"]
        allocated_users = 0
        first_long_tail_user = None
        for ind, (user, nr_jobs) in enumerate(user_lot):
            if user in user_to_id:
                continue
            if not self.config["fill_with_user_firstletter"]:
                if allocated_users < len(user_symbols):
                    user_to_id[user] = utils.ColorStr(user_symbols[allocated_users], "Red_L")
                    allocated_users += 1
                else:
                    user_to_id[user] = utils.ColorStr(SYMBOL_LONG_TAIL_USER, "Red_L")
                    if first_long_tail_user is None:
                        first_long_tail_user = user
            else:
                if user.startswith(SYMBOL_LONG_TAIL_USER) or user.startswith(config["non_existent_node_symbol"]) or user.startswith(SYMBOL_UNKNOWN_NODE_STATE) or user.startswith("_"):
                    user_to_id[user] = utils.ColorStr(SYMBOL_LONG_TAIL_USER, "Red_L")
                else:
                    first_letter = user[0]
                    if first_letter not in user_to_id.values() and first_letter not in _reserved_user_symbols(config):
                        user_to_id[user] = utils.ColorStr(first_letter, "Red_L")
                    else:
                        user_to_id[user] = utils.ColorStr(SYMBOL_LONG_TAIL_USER, "Red_L")
                    if str(user_to_id[user]) == SYMBOL_LONG_TAIL_USER and first_long_tail_user is None:
                        first_long_tail_user = user

        if first_long_tail_user:
            logging.warning(
                "Long tail user symbol %s represents %s and any later user that cannot fit in the configured symbol pool." % (SYMBOL_LONG_TAIL_USER, first_long_tail_user)
            )
        return user_to_id

    def _create_user_job_counts(self, user_names, job_states, state_abbrevs):
        user_job_counts = defaultdict_counter()
        for job_state, user_name in zip(job_states, user_names):
            try:
                abbr, full_name = state_abbrevs[job_state]
            except KeyError:
                raise JobNotFound(job_state)

            user_job_counts[abbr][user_name] += 1
        return user_job_counts

    def _create_account_jobs_table(self, user_to_id, account_jobs_table):
        new_account_jobs_table = []
        for _id, running, queued, total, user, nr_users in account_jobs_table:
            try:
                assigned_id = user_to_id[user]
            except KeyError:
                user_to_id[user] = utils.ColorStr(_id, "Red_L")
                assigned_id = user_to_id[user]
            new_account_jobs_table.append([assigned_id, running, queued, total, user, nr_users])
        return new_account_jobs_table, user_to_id

    def _aggregate_user_or_account_counts(self, jobs, key_name, user_or_account_name):
        return len([job for job in jobs.values() if getattr(job, key_name) == user_or_account_name])

    def _count_worker_node_job_core(self, worker_node):
        return sum(1 for core in worker_node["state"]["core_job_map"].values() if core)

    def _merge_core_user_maps(self, base_map, extra_map):
        merged_map = base_map.copy()
        for core, user_id in extra_map.items():
            if core not in merged_map:
                merged_map[core] = user_id
        return merged_map

    def _create_account_jobs_table(self, user_to_id, account_jobs_table):
        new_account_jobs_table = []
        for _id, running, queued, total, user, nr_users in account_jobs_table:
            try:
                assigned_id = user_to_id[user]
            except KeyError:
                user_to_id[user] = utils.ColorStr(_id, "Red_L")
                assigned_id = user_to_id[user]
            new_account_jobs_table.append([assigned_id, running, queued, total, user, nr_users])
        return new_account_jobs_table, user_to_id

    def get_worker_node_occupancy(self, job_ids, worker_nodes):
        """
        Gets the job_ids and the worker nodes and generates the matrix.

        This should work for the value of np = [nr_processors / node].
        ## "de_node" below is actually core nr.
        ## If _core line counter equals to max_corelines per worker node
        ## then go to the next worker node
        """
        user_id_jobs = dict(zip(job_ids, [x.user_name for x in self.document.jobs_dict.values()]))
        if self.config["rem_empty_corelines"] == 2:
            self.worker_nodes = self._rem_empty_corelines(worker_nodes)
        for worker_node in self.worker_nodes:
            state = worker_node["state"]
            if "np" in state:  # only show completely unavailable WNs as '#'
            