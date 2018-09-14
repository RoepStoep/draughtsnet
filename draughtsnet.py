#!/usr/bin/env python
# -*- coding: utf-8 -*-

# This file is part of the lidraughts.org draughtsnet client, an adaptation
# of fishnet by Niklas Fiekas <niklas.fiekas@backscattering.de>
# Distributed under the same license:
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

"""Distributed Scan 3.0 analysis for lidraughts.org"""

from __future__ import print_function
from __future__ import division

import argparse
import logging
import json
import time
import random
import math
import collections
import contextlib
import multiprocessing
import threading
import site
import struct
import sys
import os
import stat
import platform
import re
import textwrap
import getpass
import signal
import ctypes
import string

try:
    import requests
except ImportError:
    print("draughtsnet requires the 'requests' module.", file=sys.stderr)
    print("Try 'pip install requests' or install python-requests from your distro packages.", file=sys.stderr)
    print(file=sys.stderr)
    raise

if os.name == "posix" and sys.version_info[0] < 3:
    try:
        import subprocess32 as subprocess
    except ImportError:
        import subprocess
else:
    import subprocess

try:
    import urlparse
except ImportError:
    import urllib.parse as urlparse

try:
    import configparser
except ImportError:
    import ConfigParser as configparser

try:
    import queue
except ImportError:
    import Queue as queue

try:
    from shlex import quote as shell_quote
except ImportError:
    from pipes import quote as shell_quote

try:
    # Python 2
    input = raw_input
except NameError:
    pass

try:
    # Python 3
    DEAD_ENGINE_ERRORS = (EOFError, IOError, BrokenPipeError)
except NameError:
    # Python 2
    DEAD_ENGINE_ERRORS = (EOFError, IOError)


__version__ = "1.0.0"

__author__ = "Stefan Schermann"
__email__ = "stefan.schermann@gmail.com"
__license__ = "GPLv3+"

DEFAULT_ENDPOINT = "https://lidraughts.org/draughtsnet/"
DEFAULT_THREADS = 1
HASH_MIN = 16
HASH_DEFAULT = 256
HASH_MAX = 512
MAX_BACKOFF = 30.0
MAX_FIXED_BACKOFF = 1.0
HTTP_TIMEOUT = 15.0
STAT_INTERVAL = 60.0
DEFAULT_CONFIG = "draughtsnet.ini"
PROGRESS_REPORT_INTERVAL = 5.0
LVL_MOVETIMES = [50, 100, 150, 200, 300, 400, 500, 1000]
LVL_DEPTHS = [1, 2, 3, 4, 5, 8, 13, 18]


def intro():
    return "Draughtsnet %s - Distributed Scan 3.0 analysis for lidraughts.org" % __version__


PROGRESS = 15
ENGINE = 5
logging.addLevelName(PROGRESS, "PROGRESS")
logging.addLevelName(ENGINE, "ENGINE")


class LogFormatter(logging.Formatter):
    def format(self, record):
        # Format message
        msg = super(LogFormatter, self).format(record)

        # Add level name
        if record.levelno in [logging.INFO, PROGRESS]:
            with_level = msg
        else:
            with_level = "%s: %s" % (record.levelname, msg)

        # Add thread name
        if record.threadName == "MainThread":
            return with_level
        else:
            return "%s: %s" % (record.threadName, with_level)


class CollapsingLogHandler(logging.StreamHandler):
    def __init__(self, stream=sys.stdout):
        super(CollapsingLogHandler, self).__init__(stream)
        self.last_level = logging.INFO
        self.last_len = 0

    def emit(self, record):
        try:
            if self.last_level == PROGRESS:
                if record.levelno == PROGRESS:
                    self.stream.write("\r")
                else:
                    self.stream.write("\n")

            msg = self.format(record)
            if record.levelno == PROGRESS:
                self.stream.write(msg.ljust(self.last_len))
                self.last_len = max(len(msg), self.last_len)
            else:
                self.last_len = 0
                self.stream.write(msg)
                self.stream.write("\n")

            self.last_level = record.levelno
            self.flush()
        except Exception:
            self.handleError(record)


class TailLogHandler(logging.Handler):
    def __init__(self, capacity, max_level, flush_level, target_handler):
        super(TailLogHandler, self).__init__()
        self.buffer = collections.deque(maxlen=capacity)
        self.max_level = max_level
        self.flush_level = flush_level
        self.target_handler = target_handler

    def emit(self, record):
        if record.levelno < self.max_level:
            self.buffer.append(record)

        if record.levelno >= self.flush_level:
            while self.buffer:
                record = self.buffer.popleft()
                self.target_handler.handle(record)


class CensorLogFilter(logging.Filter):
    def __init__(self, keyword):
        self.keyword = keyword

    def censor(self, msg):
        try:
            # Python 2
            if not isinstance(msg, basestring):
                return msg
        except NameError:
            # Python 3
            if not isinstance(msg, str):
                return msg

        if self.keyword:
            return msg.replace(self.keyword, "*" * len(self.keyword))
        else:
            return msg

    def filter(self, record):
        record.msg = self.censor(record.msg)
        record.args = tuple(self.censor(arg) for arg in record.args)
        return True


def setup_logging(verbosity, stream=sys.stdout):
    logger = logging.getLogger()
    logger.setLevel(ENGINE)

    handler = logging.StreamHandler(stream)

    if verbosity >= 3:
        handler.setLevel(ENGINE)
    elif verbosity >= 2:
        handler.setLevel(logging.DEBUG)
    elif verbosity >= 1:
        handler.setLevel(PROGRESS)
    else:
        if stream.isatty():
            handler = CollapsingLogHandler(stream)
            handler.setLevel(PROGRESS)
        else:
            handler.setLevel(logging.INFO)

    if verbosity < 2:
        logging.getLogger("urllib3").setLevel(logging.WARNING)

    tail_target = logging.StreamHandler(stream)
    tail_target.setFormatter(LogFormatter())
    logger.addHandler(TailLogHandler(35, handler.level, logging.ERROR, tail_target))

    handler.setFormatter(LogFormatter())
    logger.addHandler(handler)


def base_url(url):
    url_info = urlparse.urlparse(url)
    return "%s://%s/" % (url_info.scheme, url_info.hostname)


class ConfigError(Exception):
    pass


class UpdateRequired(Exception):
    pass


class Shutdown(Exception):
    pass


class ShutdownSoon(Exception):
    pass


class SignalHandler(object):
    def __init__(self):
        self.ignore = False

        signal.signal(signal.SIGTERM, self.handle_term)
        signal.signal(signal.SIGINT, self.handle_int)

        try:
            signal.signal(signal.SIGUSR1, self.handle_usr1)
        except AttributeError:
            # No SIGUSR1 on Windows
            pass

    def handle_int(self, signum, frame):
        if not self.ignore:
            self.ignore = True
            raise ShutdownSoon()

    def handle_term(self, signum, frame):
        if not self.ignore:
            self.ignore = True
            raise Shutdown()

    def handle_usr1(self, signum, frame):
        if not self.ignore:
            self.ignore = True
            raise UpdateRequired()


def open_process(command, cwd=None, shell=True, _popen_lock=threading.Lock()):
    kwargs = {
        "shell": shell,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.STDOUT,
        "stdin": subprocess.PIPE,
        "bufsize": 1,  # Line buffered
        "universal_newlines": True,
    }

    if cwd is not None:
        kwargs["cwd"] = cwd

    # Prevent signal propagation from parent process
    try:
        # Windows
        kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    except AttributeError:
        # Unix
        kwargs["preexec_fn"] = os.setpgrp

    with _popen_lock:  # Work around Python 2 Popen race condition
        return subprocess.Popen(command, **kwargs)


def kill_process(p):
    try:
        # Windows
        p.send_signal(signal.CTRL_BREAK_EVENT)
    except AttributeError:
        # Unix
        os.killpg(p.pid, signal.SIGKILL)

    p.communicate()


def send(p, line):
    logging.log(ENGINE, "%s << %s", p.pid, line)
    p.stdin.write(line + "\n")
    p.stdin.flush()


def recv(p):
    while True:
        line = p.stdout.readline()
        if line == "":
            raise EOFError()

        line = line.rstrip()

        logging.log(ENGINE, "%s >> %s", p.pid, line)

        if line:
            return line


def recv_uci(p):
    command_and_args = recv(p).split(None, 1)
    if len(command_and_args) == 1:
        return command_and_args[0], ""
    elif len(command_and_args) == 2:
        return command_and_args


def uci(p):
    send(p, "hub")

    engine_info = {}
    variants = set()

    while True:
        command, arg = recv_uci(p)

        if command == "wait":
            return engine_info, variants
        elif command == "id":
            parts = arg.split()
            i = 0
            while i < len(parts):
                name_and_value = parts[i].split("=", 1)
                if len(name_and_value) == 2:
                    value = name_and_value[1]
                    if value.startswith("\""):
                        value = value[1:]
                        i += 1
                        while i < len(parts) and not parts[i].endswith("\""):
                            value += " " + parts[i]
                            i += 1
                        value += " " + parts[i][:-1]
                    engine_info[name_and_value[0]] = value
                i += 1
        elif command == "param":
            if arg.startswith("name=variant") and arg.find("type=enum") != -1:
                argvalues = arg.split("=")[-1].replace("\"", "")
                for variant in argvalues.split():
                    variants.add(variant)
        else:
            logging.warning("Unexpected engine response to uci: %s %s", command, arg)


def init(p):
    send(p, "init")
    while True:
        command, arg = recv_uci(p)
        if command == "ready":
            break
        elif command == "init":
            pass
        else:
            logging.warning("Unexpected engine response to init: %s %s", command, arg)


def ping(p):
    send(p, "ping")
    while True:
        command, arg = recv_uci(p)
        if command == "pong":
            break
        else:
            logging.warning("Unexpected engine response to ping: %s %s", command, arg)


def setoption(p, name, value):
    if value is True:
        value = "true"
    elif value is False:
        value = "false"
    elif value is None:
        value = "none"

    send(p, "set-param name=%s value=%s" % (name, value))


def go(p, position, moves, movetime=None, clock=None, depth=None, nodes=None):
    if moves and len(moves) != 0 and moves[0] != "":
        send(p, "pos pos=%s moves=\"%s\"" % (position, moves))
    else:
        send(p, "pos pos=%s" % position)

    if movetime is not None and clock is not None:
        if position[0] == 'B':
            timeleft = clock["btime"] / 100.0
        else :
            timeleft = clock["wtime"] / 100.0
        increment = clock["inc"]
        if increment == 0 and timeleft < 40.0:
            movetime *= (timeleft / 40.0)
        elif increment == 1 and timeleft < 6.0:
            movetime *= (timeleft / 6.0)

    builder = []
    builder.append("level")
    if depth is not None:
        builder.append("depth=%s" % str(depth))
    elif nodes is not None:
        if movetime is None:
            builder.append("move-time=2")
        else:
            builder.append("move-time=%s" % str(movetime))
    elif movetime is not None:
        builder.append("move-time=%s" % str(movetime))

    send(p, " ".join(builder))

    if nodes is not None:
        send(p, "go analyze")
    else:
        send(p, "go think")

    info = {}
    info["bestmove"] = None

    start = time.time()
    while True:
        command, arg = recv_uci(p)

        forcestop = False
        if command == "done":
            if len(arg) == 0:
                info["bestmove"] = "gameover"
                info["taken"] = ""
                return info
            bestmoveval = arg.split()[0]
            if bestmoveval and bestmoveval.find("=") != -1:
                bestmove = bestmoveval.split("=")[1]
                if bestmove.find("x") != -1:
                    fields = bestmove.split("x")
                    origdest = fields[:2]
                    taken = fields[2:]
                else:
                    origdest = bestmove.split("-")[:2]
                    taken = []
                if len(origdest) == 2:
                    info["bestmove"] = "%02d%02d" % (int(origdest[0]), int(origdest[1]))
                alltaken = ""
                for t in taken:
                    alltaken += "%02d" % int(t)
                info["taken"] = alltaken
            return info
        elif command == "info":
            arg = arg or ""

            # Parse all other parameters
            cur_nodes = 0
            parts = arg.split()
            i = 0
            while i < len(parts):
                name_and_value = parts[i].split("=", 1)
                if len(name_and_value) == 2:
                    value = name_and_value[1]
                    if value.startswith("\""):
                        value = value[1:]
                        i += 1
                        while i < len(parts) and not parts[i].endswith("\""):
                            value += " " + parts[i]
                            i += 1
                        value += " " + parts[i][:-1]
                    if name_and_value[0] in ["nodes", "depth"]:
                        info[name_and_value[0]] = int(value)
                    else:
                        info[name_and_value[0]] = value
                    if name_and_value[0] == "nodes":
                        cur_nodes = int(value)
                i += 1

            # Check if we have reached the node count
            if nodes is not None and cur_nodes >= nodes:
                forcestop = True
        else:
            logging.warning("Unexpected engine response to go: %s %s", command, arg)

        # Force play if movetime is exceeded (not exact as we only reach this point after the engine produces output)
        if forcestop or (movetime is not None and time.time() - start > movetime):
            send(p, "stop")


def set_variant_options(p, variant):
    variant = variant.lower()

    if variant in ["standard", "fromposition"]:
        setoption(p, "variant", "normal")
    else:
        setoption(p, "variant", variant)


class ProgressReporter(threading.Thread):
    def __init__(self, queue_size, conf):
        super(ProgressReporter, self).__init__()
        self.http = requests.Session()
        self.conf = conf

        self.queue = queue.Queue(maxsize=queue_size)
        self._poison_pill = object()

    def send(self, job, result):
        path = "analysis/%s" % job["work"]["id"]
        data = json.dumps(result).encode("utf-8")
        try:
            self.queue.put_nowait((path, data))
        except queue.Full:
            logging.debug("Could not keep up with progress reports. Dropping one.")

    def stop(self):
        while not self.queue.empty():
            self.queue.get_nowait()
        self.queue.put(self._poison_pill)

    def run(self):
        while True:
            item = self.queue.get()
            if item == self._poison_pill:
                return

            path, data = item

            try:
                response = self.http.post(get_endpoint(self.conf, path),
                                          data=data,
                                          timeout=HTTP_TIMEOUT)
                if response.status_code == 429:
                    logging.error("Too many requests. Suspending progress reports for 60s ...")
                    time.sleep(60.0)
                elif response.status_code != 204:
                    logging.error("Expected status 204 for progress report, got %d", response.status_code)
            except requests.RequestException as err:
                logging.warning("Could not send progress report (%s). Continuing.", err)


class Worker(threading.Thread):
    def __init__(self, conf, threads, memory, progress_reporter, selfplay_lvl, selfplay_rounds):
        super(Worker, self).__init__()
        self.conf = conf
        self.threads = threads
        self.memory = memory

        self.progress_reporter = progress_reporter
        self.selfplay = selfplay_lvl
        self.selfplay_rounds = selfplay_rounds

        self.alive = True
        self.fatal_error = None
        self.finished = threading.Event()
        self.sleep = threading.Event()
        self.status_lock = threading.RLock()

        self.nodes = 0
        self.positions = 0

        self.scan_lock = threading.RLock()
        self.scan = None
        self.scan_info = None

        self.job = None
        self.backoff = start_backoff(self.conf)

        self.http = requests.Session()
        self.http.mount("http://", requests.adapters.HTTPAdapter(max_retries=1))
        self.http.mount("https://", requests.adapters.HTTPAdapter(max_retries=1))

    def set_name(self, name):
        self.name = name
        self.progress_reporter.name = "%s (P)" % (name, )

    def stop(self):
        with self.status_lock:
            self.alive = False
            self.kill_scan()
            self.sleep.set()

    def stop_soon(self):
        with self.status_lock:
            self.alive = False
            self.sleep.set()

    def is_alive(self):
        with self.status_lock:
            return self.alive

    def run(self):
        try:
            while self.is_alive():
                if 0 < self.selfplay <= 8:
                    self.run_selfplay()
                    return
                else:
                    self.run_inner()
        except UpdateRequired as error:
            self.fatal_error = error
        except Exception as error:
            self.fatal_error = error
            logging.exception("Fatal error in worker")
        finally:
            self.finished.set()

    def run_selfplay(self):
        try:

            # Check if the engine is still alive and start, if necessary
            self.start_scan()

            logging.info(" ### Playing %d games against self, level %d",
                         self.selfplay_rounds, self.selfplay)

            # Play 200 games against a stronger version of self from starting position
            wins = 0
            losses = 0
            draws = 0
            for i in range(self.selfplay_rounds):
                game_start = time.time()
                threefold = {}
                drawrule = 0
                move_nr = 1
                moves = ""
                pos = "Wbbbbbbbbbbbbbbbbbbbbeeeeeeeeeewwwwwwwwwwwwwwwwwwww"
                newpos = list(pos)
                white_playing = True
                self_playing = random.choice([True, False])
                while self.is_alive():

                    send(self.scan, "new-game")

                    if self_playing:
                        movetime = round(LVL_MOVETIMES[self.selfplay - 1] / (1000 * self.threads * 0.9 ** (self.threads - 1)), 2)
                        depth = LVL_DEPTHS[self.selfplay - 1]
                    else:
                        movetime = round(1.5 * LVL_MOVETIMES[7] / (1000 * self.threads * 0.9 ** (self.threads - 1)), 2)
                        depth = LVL_DEPTHS[7] + 2

                    start = time.time()
                    part = go(self.scan, pos, moves,
                              movetime=movetime, clock=None,
                              depth=depth)
                    end = time.time()

                    bestmove = part["bestmove"]
                    taken = part["taken"]

                    if len(moves) == 0:
                        newpos = list(pos)
                    whiteK = 0
                    whiteM = 0
                    blackK = 0
                    blackM = 0
                    for piece in newpos[1:]:
                        if piece == "w":
                            whiteM += 1
                        elif piece == "W":
                            whiteK += 1
                        elif piece == "b":
                            blackM += 1
                        elif piece == "B":
                            blackK += 1
                    white = whiteK + whiteM
                    black = blackK + blackM

                    if bestmove == "gameover":
                        if self_playing:
                            losses += 1
                            logging.log(PROGRESS, "Game %d: %d moves - loss in %0.3fs" % (i + 1, move_nr, time.time() - game_start))
                        else:
                            wins += 1
                            logging.log(PROGRESS, "Game %d: %d moves - win in %0.3fs" % (i + 1, move_nr, time.time() - game_start))
                        break

                    # Detect material drawing rules
                    if white + black > 2 and len(taken) != 0:
                        drawrule = 0
                    if white + black == 4 and (white == 1 or black == 1) and whiteK != 0 and blackK != 0:
                        drawrule += 1
                        if drawrule > 32:
                            draws += 1
                            logging.log(PROGRESS, "Game %d: %d moves - draw by 16 move rule in %0.3fs" % (i + 1, move_nr, time.time() - game_start))
                            break
                    elif white + black <= 3 and whiteK != 0 and blackK != 0:
                        drawrule += 1
                        if drawrule > 10:
                            draws += 1
                            logging.log(PROGRESS, "Game %d: %d moves - draw by 5 move rule in %0.3fs" % (i + 1, move_nr, time.time() - game_start))
                            break

                    origdest = list(map(''.join, zip(*[iter(bestmove)] * 2)))
                    orig = int(origdest[0])
                    dest = int(origdest[1])

                    newpos[dest] = newpos[orig]
                    newpos[orig] = "e"
                    if white_playing and int(dest) <= 5:
                        newpos[dest] = "W"
                    elif not white_playing and int(dest) >= 46:
                        newpos[dest] = "B"
                    takestring = ""
                    for takes in list(map(''.join, zip(*[iter(taken)] * 2))):
                        takepos = int(takes)
                        newpos[takepos] = "e"
                        takestring += "x%s" % str(takepos)

                    if newpos[dest] == "W" or newpos[dest] == "B":
                        if taken != "":
                            threefold = {}
                        else:
                            if white_playing:
                                testpos = "B" + "".join(newpos[1:])
                            else:
                                testpos = "W" + "".join(newpos[1:])
                            threefold[testpos] = threefold.get(testpos, 0) + 1
                            if threefold[testpos] == 3:
                                draws += 1
                                logging.log(PROGRESS,
                                            "Game %d: %d moves - drawn by threefold repetition in %0.3fs" % (i + 1, move_nr, time.time() - game_start))
                                break

                        # Move history is required for repetition, repetition is only possible after a king move
                        if len(moves) != 0:
                            moves += " "
                        if taken != "":
                            moves += "%sx%s%s" % (str(orig), str(dest), takestring)
                            drawrule = 0
                        else:
                            moves += "%s-%s" % (str(orig), str(dest))
                            drawrule += 1
                            if drawrule > 50:
                                draws += 1  # 25 kingmoves each without capture
                                logging.log(PROGRESS, "Game %d: %d moves - draw by 25 move rule in %0.3fs" % (i + 1, move_nr, time.time() - game_start))
                                break
                    else:
                        threefold = {}
                        if white + black > 4:
                            drawrule = 0
                        if white_playing:
                            pos = "B" + "".join(newpos[1:])
                        else:
                            pos = "W" + "".join(newpos[1:])
                        moves = ""

                    if taken != "":
                        logmove = "%sx%s" % (str(orig), str(dest))
                    else:
                        logmove = "%s-%s" % (str(orig), str(dest))
                    if white_playing:
                        logmove = "%s. %s" % (str(move_nr), logmove)
                    else:
                        logmove = "%s... %s" % (str(move_nr), logmove)
                    logging.debug("%0.3fs, depth %d: %s", end - start, part.get("depth", 0), logmove)

                    white_playing = not white_playing
                    self_playing = not self_playing

                    if white_playing:
                        move_nr += 1

                    self.nodes += part.get("nodes", 0)
                    self.positions += 1

            logging.info(" ### Finished level %d: +%d -%d =%d",
                        self.selfplay, wins, losses, draws)

            # done
            self.kill_scan()
            return

        except UpdateRequired as error:
            self.fatal_error = error
        except Exception as error:
            self.fatal_error = error
            logging.exception("Fatal error in worker")
        finally:
            self.finished.set()

    def run_inner(self):
        try:
            # Check if the engine is still alive and start, if necessary
            self.start_scan()

            # Do the next work unit
            path, request = self.work()
        except DEAD_ENGINE_ERRORS:
            alive = self.is_alive()
            if alive:
                t = next(self.backoff)
                logging.exception("Engine process has died. Backing off %0.1fs", t)

            # Abort current job
            self.abort_job()

            if alive:
                self.sleep.wait(t)
                self.kill_scan()

            return

        try:
            # Report result and fetch next job
            response = self.http.post(get_endpoint(self.conf, path),
                                      json=request,
                                      timeout=HTTP_TIMEOUT)
        except requests.RequestException as err:
            self.job = None
            t = next(self.backoff)
            logging.error("Backing off %0.1fs after failed request (%s)", t, err)
            self.sleep.wait(t)
        else:
            if response.status_code == 204:
                self.job = None
                t = next(self.backoff)
                logging.debug("No job found. Backing off %0.1fs", t)
                self.sleep.wait(t)
            elif response.status_code == 202:
                logging.debug("Got job: %s", response.text)
                self.job = response.json()
                self.backoff = start_backoff(self.conf)
            elif 500 <= response.status_code <= 599:
                self.job = None
                t = next(self.backoff)
                logging.error("Server error: HTTP %d %s. Backing off %0.1fs", response.status_code, response.reason, t)
                self.sleep.wait(t)
            elif 400 <= response.status_code <= 499:
                self.job = None
                t = next(self.backoff) + (60 if response.status_code == 429 else 0)
                try:
                    logging.debug("Client error: HTTP %d %s: %s", response.status_code, response.reason, response.text)
                    error = response.json()["error"]
                    logging.error(error)

                    if "Please restart draughtsnet to upgrade." in error:
                        logging.error("Stopping worker for update.")
                        raise UpdateRequired()
                except (KeyError, ValueError):
                    logging.error("Client error: HTTP %d %s. Backing off %0.1fs. Request was: %s",
                                  response.status_code, response.reason, t, json.dumps(request))
                self.sleep.wait(t)
            else:
                self.job = None
                t = next(self.backoff)
                logging.error("Unexpected HTTP status for acquire: %d", response.status_code)
                self.sleep.wait(t)

    def abort_job(self):
        if self.job is None:
            return

        logging.debug("Aborting job %s", self.job["work"]["id"])

        try:
            response = requests.post(get_endpoint(self.conf, "abort/%s" % self.job["work"]["id"]),
                                     data=json.dumps(self.make_request()),
                                     timeout=HTTP_TIMEOUT)
            if response.status_code == 204:
                logging.info("Aborted job %s", self.job["work"]["id"])
            else:
                logging.error("Unexpected HTTP status for abort: %d", response.status_code)
        except requests.RequestException:
            logging.exception("Could not abort job. Continuing.")

        self.job = None

    def kill_scan(self):
        with self.scan_lock:
            if self.scan:
                try:
                    kill_process(self.scan)
                except OSError:
                    logging.exception("Failed to kill engine process.")
                self.scan = None

    def start_scan(self):
        with self.scan_lock:
            # Check if already running.
            if self.scan and self.scan.poll() is None:
                return

            # Start process
            self.scan = open_process(get_scan_command(self.conf, False),
                                          get_engine_dir(self.conf))

        self.scan_info, _ = uci(self.scan)
        logging.info("Started %s, threads: %s (%d), pid: %d",
                     self.scan_info.get("name", "Scan <?>"),
                     "+" * self.threads, self.threads, self.scan.pid)

        # Prepare UCI options
        self.scan_info["options"] = {}
        self.scan_info["options"]["threads"] = str(self.threads)
        self.scan_info["options"]["tt-size"] = str(math.floor(math.log(self.memory * 1024 * 1024 / 16, 2)))

        # Custom options
        if self.conf.has_section("Scan"):
            for name, value in self.conf.items("Scan"):
                self.scan_info["options"][name] = value

        # Set UCI options
        for name, value in self.scan_info["options"].items():
            setoption(self.scan, name, value)

        init(self.scan)

    def make_request(self):
        return {
            "draughtsnet": {
                "version": __version__,
                "python": platform.python_version(),
                "apikey": get_key(self.conf),
            },
            "scan": self.scan_info,
        }

    def work(self):
        result = self.make_request()

        if self.job and self.job["work"]["type"] == "analysis":
            result = self.analysis(self.job)
            return "analysis" + "/" + self.job["work"]["id"], result
        elif self.job and self.job["work"]["type"] == "move":
            result = self.bestmove(self.job)
            return "move" + "/" + self.job["work"]["id"], result
        else:
            if self.job:
                logging.error("Invalid job type: %s", self.job["work"]["type"])

            return "acquire", result

    def job_name(self, job, ply=None):
        builder = []
        if job.get("game_id"):
            builder.append(base_url(get_endpoint(self.conf)))
            builder.append(job["game_id"])
        else:
            builder.append(job["work"]["id"])
        if ply is not None:
            builder.append("#")
            builder.append(str(ply))
        return "".join(builder)

    def bestmove(self, job):
        lvl = job["work"]["level"]
        variant = job.get("variant", "standard")
        moves = job["moves"].split(" ")

        logging.debug("Playing %s (%s) with lvl %d",
                      self.job_name(job), variant, lvl)

        send(self.scan, "new-game")

        movetime = round(LVL_MOVETIMES[lvl - 1] / (1000 * self.threads * 0.9 ** (self.threads - 1)), 2)

        start = time.time()
        part = go(self.scan, job["position"], moves,
                  movetime=movetime, clock=job["work"].get("clock"),
                  depth=LVL_DEPTHS[lvl - 1])
        end = time.time()

        logging.log(PROGRESS, "Played move in %s (%s) with lvl %d: %0.3fs elapsed, depth %d",
                    self.job_name(job), variant,
                    lvl, end - start, part.get("depth", 0))

        self.nodes += part.get("nodes", 0)
        self.positions += 1

        result = self.make_request()
        result["move"] = {
            "bestmove": part["bestmove"],
            "taken": part["taken"]
        }
        return result

    def analysis(self, job):
        variant = job.get("variant", "standard")
        moves = job["moves"].split(" ")

        result = self.make_request()
        result["analysis"] = [None for _ in range(len(moves) + 1)]
        start = last_progress_report = time.time()

        set_variant_options(self.scan, variant)
        setoption(self.scan, "Skill Level", 20)
        setoption(self.scan, "UCI_AnalyseMode", True)
        send(self.scan, "ucinewgame")

        nodes = job.get("nodes") or 3500000
        skip = job.get("skipPositions", [])

        num_positions = 0

        for ply in range(len(moves), -1, -1):
            if ply in skip:
                result["analysis"][ply] = {"skipped": True}
                continue

            if last_progress_report + PROGRESS_REPORT_INTERVAL < time.time():
                if self.progress_reporter:
                    self.progress_reporter.send(job, result)
                last_progress_report = time.time()

            logging.log(PROGRESS, "Analysing %s: %s",
                        variant, self.job_name(job, ply))

            part = go(self.scan, job["position"], moves[0:ply],
                      nodes=nodes, movetime=4000)

            if "mate" not in part["score"] and "time" in part and part["time"] < 100:
                logging.warning("Very low time reported: %d ms.", part["time"])

            if "nps" in part and part["nps"] >= 100000000:
                logging.warning("Dropping exorbitant nps: %d", part["nps"])
                del part["nps"]

            self.nodes += part.get("nodes", 0)
            self.positions += 1
            num_positions += 1

            result["analysis"][ply] = part

        end = time.time()

        if num_positions:
            logging.info("%s took %0.1fs (%0.2fs per position)",
                         self.job_name(job),
                         end - start, (end - start) / num_positions)
        else:
            logging.info("%s done (nothing to do)", self.job_name(job))

        return result


def detect_cpu_capabilities():
    # Detects support for popcnt and pext instructions
    vendor, modern, bmi2 = "", False, False

    # Run cpuid in subprocess for robustness in case of segfaults
    cmd = []
    cmd.append(sys.executable)
    if __package__ is not None:
        cmd.append("-m")
        cmd.append(os.path.splitext(os.path.basename(__file__))[0])
    else:
        cmd.append(__file__)
    cmd.append("cpuid")

    process = open_process(cmd, shell=False)

    # Parse output
    while True:
        line = process.stdout.readline()
        if not line:
            break

        line = line.rstrip()
        logging.debug("cpuid >> %s", line)
        if not line:
            continue

        columns = line.split()
        if columns[0] == "CPUID":
            pass
        elif len(columns) == 5 and all(all(c in string.hexdigits for c in col) for col in columns):
            eax, a, b, c, d = [int(col, 16) for col in columns]

            # vendor
            if eax == 0:
                vendor = struct.pack("III", b, d, c).decode("utf-8")

            # popcnt
            if eax == 1 and c & (1 << 23):
                modern = True

            # pext
            if eax == 7 and b & (1 << 8):
                bmi2 = True
        else:
            logging.warning("Unexpected cpuid output: %s", line)

    # Done
    process.communicate()
    if process.returncode != 0:
        logging.error("cpuid exited with status code %d", process.returncode)

    return vendor, modern, bmi2


def scan_filename():
    machine = platform.machine().lower()

    if os.name == "nt":
        return "scan.exe"
    else:
        return "scan"


def load_conf(args):
    conf = configparser.ConfigParser()
    conf.add_section("Draughtsnet")
    conf.add_section("Scan")

    if not args.no_conf:
        if not args.conf and not os.path.isfile(DEFAULT_CONFIG):
            return configure(args)

        config_file = args.conf or DEFAULT_CONFIG
        logging.debug("Using config file: %s", config_file)

        if not conf.read(config_file):
            raise ConfigError("Could not read config file: %s" % config_file)

    if hasattr(args, "engine_dir") and args.engine_dir is not None:
        conf.set("Draughtsnet", "EngineDir", args.engine_dir)
    if hasattr(args, "scan_command") and args.scan_command is not None:
        conf.set("Draughtsnet", "ScanCommand", args.scan_command)
    if hasattr(args, "key") and args.key is not None:
        conf.set("Draughtsnet", "Key", args.key)
    if hasattr(args, "cores") and args.cores is not None:
        conf.set("Draughtsnet", "Cores", args.cores)
    if hasattr(args, "memory") and args.memory is not None:
        conf.set("Draughtsnet", "Memory", args.memory)
    if hasattr(args, "threads") and args.threads is not None:
        conf.set("Draughtsnet", "Threads", str(args.threads))
    if hasattr(args, "endpoint") and args.endpoint is not None:
        conf.set("Draughtsnet", "Endpoint", args.endpoint)
    if hasattr(args, "fixed_backoff") and args.fixed_backoff is not None:
        conf.set("Draughtsnet", "FixedBackoff", str(args.fixed_backoff))
    for option_name, option_value in args.setoption:
        conf.set("Scan", option_name.lower(), option_value)

    logging.getLogger().addFilter(CensorLogFilter(conf_get(conf, "Key")))

    return conf


def config_input(prompt, validator, out):
    while True:
        if out == sys.stdout:
            inp = input(prompt)
        else:
            if prompt:
                out.write(prompt)
                out.flush()

            inp = input()

        try:
            return validator(inp)
        except ConfigError as error:
            print(error, file=out)


def configure(args):
    if sys.stdout.isatty():
        out = sys.stdout
        try:
            # Unix: Importing for its side effect
            import readline  # noqa: F401
        except ImportError:
            # Windows
            pass
    else:
        out = sys.stderr

    print(file=out)
    print("### Configuration", file=out)
    print(file=out)

    conf = configparser.ConfigParser()
    conf.add_section("Draughtsnet")
    conf.add_section("Scan")

    # Ensure the config file is going to be writable
    config_file = os.path.abspath(args.conf or DEFAULT_CONFIG)
    if os.path.isfile(config_file):
        conf.read(config_file)
        with open(config_file, "r+"):
            pass
    else:
        with open(config_file, "w"):
            pass
        os.remove(config_file)

    # Scan working directory
    engine_dir = config_input("Engine working directory (default: %s): " % os.path.abspath("."),
                              validate_engine_dir, out)
    conf.set("Draughtsnet", "EngineDir", engine_dir)

    # Scan command
    print(file=out)
    scan_command = config_input("Command to run scan in hub mode (default: scan.exe hub): ",
                                     lambda v: validate_scan_command(v, conf),
                                     out)

    conf.set("Draughtsnet", "ScanCommand", scan_command)
    print(file=out)

    # Cores
    max_cores = multiprocessing.cpu_count()
    default_cores = max(1, max_cores - 1)
    cores = config_input("Number of cores to use for engine threads (default %d, max %d): " % (default_cores, max_cores),
                         validate_cores, out)
    conf.set("Draughtsnet", "Cores", str(cores))

    # Advanced options
    endpoint = args.endpoint or DEFAULT_ENDPOINT
    if config_input("Configure advanced options? (default: no) ", parse_bool, out):
        endpoint = config_input("Draughtsnet API endpoint (default: %s): " % (endpoint, ), lambda inp: validate_endpoint(inp, endpoint), out)

    conf.set("Draughtsnet", "Endpoint", endpoint)

    # Change key?
    key = None
    if conf.has_option("Draughtsnet", "Key"):
        if not config_input("Change draughtsnet key? (default: no) ", parse_bool, out):
            key = conf.get("Draughtsnet", "Key")

    # Key
    if key is None:
        status = "https://lidraughts.org/get-draughtsnet" if is_production_endpoint(conf) else "probably not required"
        key = config_input("Personal draughtsnet key (append ! to force, %s): " % status,
                           lambda v: validate_key(v, conf, network=True), out)
    conf.set("Draughtsnet", "Key", key)
    logging.getLogger().addFilter(CensorLogFilter(key))

    # Confirm
    print(file=out)
    while not config_input("Done. Write configuration to %s now? (default: yes) " % (config_file, ),
                           lambda v: parse_bool(v, True), out):
        pass

    # Write configuration
    with open(config_file, "w") as f:
        conf.write(f)

    print("Configuration saved.", file=out)
    return conf


def validate_engine_dir(engine_dir):
    if not engine_dir or not engine_dir.strip():
        return os.path.abspath(".")

    engine_dir = os.path.abspath(os.path.expanduser(engine_dir.strip()))

    if not os.path.isdir(engine_dir):
        raise ConfigError("EngineDir not found: %s" % engine_dir)

    return engine_dir


def validate_scan_command(scan_command, conf):
    if not scan_command or not scan_command.strip():
        scan_command = "scan.exe hub"

    scan_command = scan_command.strip()
    engine_dir = get_engine_dir(conf)

    # Ensure the required options are supported
    process = open_process(scan_command, engine_dir)
    _, variants = uci(process)
    kill_process(process)

    logging.debug("Supported variants: %s", ", ".join(variants))

    required_variants = set(["normal"])
    missing_variants = required_variants.difference(variants)
    if missing_variants:
        raise ConfigError("Ensure you are using Scan 3.0. "
                          "Unsupported variants: %s" % ", ".join(missing_variants))

    return scan_command


def parse_bool(inp, default=False):
    if not inp:
        return default

    inp = inp.strip().lower()
    if not inp:
        return default

    if inp in ["y", "j", "yes", "yep", "true", "t", "1", "ok"]:
        return True
    elif inp in ["n", "no", "nop", "nope", "f", "false", "0"]:
        return False
    else:
        raise ConfigError("Not a boolean value: %s", inp)


def validate_cores(cores):
    if not cores or cores.strip().lower() == "auto":
        return max(1, multiprocessing.cpu_count() - 1)

    if cores.strip().lower() == "all":
        return multiprocessing.cpu_count()

    try:
        cores = int(cores.strip())
    except ValueError:
        raise ConfigError("Number of cores must be an integer")

    if cores < 1:
        raise ConfigError("Need at least one core")

    if cores > multiprocessing.cpu_count():
        raise ConfigError("At most %d cores available on your machine " % multiprocessing.cpu_count())

    return cores


def validate_threads(threads, conf):
    cores = validate_cores(conf_get(conf, "Cores"))

    if not threads or str(threads).strip().lower() == "auto":
        return min(DEFAULT_THREADS, cores)

    try:
        threads = int(str(threads).strip())
    except ValueError:
        raise ConfigError("Number of threads must be an integer")

    if threads < 1:
        raise ConfigError("Need at least one thread per engine process")

    if threads > cores:
        raise ConfigError("%d cores is not enough to run %d threads" % (cores, threads))

    return threads


def validate_memory(memory, conf):
    cores = validate_cores(conf_get(conf, "Cores"))
    threads = validate_threads(conf_get(conf, "Threads"), conf)
    processes = cores // threads

    if not memory or not memory.strip() or memory.strip().lower() == "auto":
        return processes * HASH_DEFAULT

    try:
        memory = int(memory.strip())
    except ValueError:
        raise ConfigError("Memory must be an integer")

    if memory < processes * HASH_MIN:
        raise ConfigError("Not enough memory for a minimum of %d x %d MB in hash tables" % (processes, HASH_MIN))

    if memory > processes * HASH_MAX:
        raise ConfigError("Can not reasonably use more than %d x %d MB = %d MB for hash tables" % (processes, HASH_MAX, processes * HASH_MAX))

    return memory


def validate_endpoint(endpoint, default=DEFAULT_ENDPOINT):
    if not endpoint or not endpoint.strip():
        return default

    if not endpoint.endswith("/"):
        endpoint += "/"

    url_info = urlparse.urlparse(endpoint)
    if url_info.scheme not in ["http", "https"]:
        raise ConfigError("Endpoint does not have http:// or https:// URL scheme")

    return endpoint


def validate_key(key, conf, network=False):
    if not key or not key.strip():
        if is_production_endpoint(conf):
            raise ConfigError("Draughtsnet key required")
        else:
            return ""

    key = key.strip()

    network = network and not key.endswith("!")
    key = key.rstrip("!").strip()

    if not re.match(r"^[a-zA-Z0-9]+$", key):
        raise ConfigError("Draughtsnet key is expected to be alphanumeric")

    if network:
        response = requests.get(get_endpoint(conf, "key/%s" % key), timeout=HTTP_TIMEOUT)
        if response.status_code == 404:
            raise ConfigError("Invalid or inactive draughtsnet key")
        else:
            response.raise_for_status()

    return key


def conf_get(conf, key, default=None, section="Draughtsnet"):
    if not conf.has_section(section):
        return default
    elif not conf.has_option(section, key):
        return default
    else:
        return conf.get(section, key)


def get_engine_dir(conf):
    return validate_engine_dir(conf_get(conf, "EngineDir"))


def get_scan_command(conf, update=True):
    scan_command = validate_scan_command(conf_get(conf, "ScanCommand"), conf)
    if not scan_command:
        filename = scan_filename() + " hub"
        return validate_scan_command(os.path.join(".", filename), conf)
    else:
        return scan_command


def get_endpoint(conf, sub=""):
    return urlparse.urljoin(validate_endpoint(conf_get(conf, "Endpoint")), sub)


def is_production_endpoint(conf):
    endpoint = validate_endpoint(conf_get(conf, "Endpoint"))
    hostname = urlparse.urlparse(endpoint).hostname
    return hostname == "lidraughts.org" or hostname.endswith(".lidraughts.org")


def get_key(conf):
    return validate_key(conf_get(conf, "Key"), conf, network=False)


def start_backoff(conf):
    if parse_bool(conf_get(conf, "FixedBackoff")):
        while True:
            yield random.random() * MAX_FIXED_BACKOFF
    else:
        backoff = 1
        while True:
            yield 0.5 * backoff + 0.5 * backoff * random.random()
            backoff = min(backoff + 1, MAX_BACKOFF)


def cmd_run(args):
    conf = load_conf(args)

    scan_command = validate_scan_command(conf_get(conf, "ScanCommand"), conf)
    if not scan_command:
        raise ConfigError("Ensure you are using Scan 3.0. "
                          "Invalid command: %s" % scan_command)

    print()
    print("### Checking configuration ...")
    print()
    print("Python:           %s (with requests %s)" % (platform.python_version(), requests.__version__))
    print("EngineDir:        %s" % get_engine_dir(conf))
    print("ScanCommand:      %s" % scan_command)
    print("Key:              %s" % (("*" * len(get_key(conf))) or "(none)"))

    cores = validate_cores(conf_get(conf, "Cores"))
    print("Cores:            %d" % cores)

    threads = validate_threads(conf_get(conf, "Threads"), conf)
    instances = max(1, cores // threads)
    print("Engine processes: %d (each ~%d threads)" % (instances, threads))
    memory = validate_memory(conf_get(conf, "Memory"), conf)
    print("Memory:           %d MB" % memory)
    endpoint = get_endpoint(conf)
    warning = "" if endpoint.startswith("https://") else " (WARNING: not using https)"
    print("Endpoint:         %s%s" % (endpoint, warning))
    print("FixedBackoff:     %s" % parse_bool(conf_get(conf, "FixedBackoff")))
    print()

    if conf.has_section("Scan") and conf.items("Scan"):
        print("Using custom engine options is discouraged:")
        for name, value in conf.items("Scan"):
            if name.lower() == "hash":
                hint = " (use --memory instead)"
            elif name.lower() == "threads":
                hint = " (use --threads-per-process instead)"
            else:
                hint = ""
            print(" * %s = %s%s" % (name, value, hint))
        print()

    print("### Starting workers ...")
    print()

    buckets = [0] * instances
    for i in range(0, cores):
        buckets[i % instances] += 1

    progress_reporter = ProgressReporter(len(buckets) + 4, conf)
    progress_reporter.setDaemon(True)
    progress_reporter.start()

    workers = [Worker(conf, bucket, memory // instances, progress_reporter, 0, 0) for bucket in buckets]

    # Start all threads
    for i, worker in enumerate(workers):
        worker.set_name("><> %d" % (i + 1))
        worker.setDaemon(True)
        worker.start()

    # Wait while the workers are running
    try:
        # Let SIGTERM and SIGINT gracefully terminate the program
        handler = SignalHandler()

        try:
            while True:
                # Check worker status
                for _ in range(int(max(1, STAT_INTERVAL / len(workers)))):
                    for worker in workers:
                        worker.finished.wait(1.0)
                        if worker.fatal_error:
                            raise worker.fatal_error

                # Log stats
                logging.info("[draughtsnet v%s] Analyzed %d positions, crunched %d million nodes",
                             __version__,
                             sum(worker.positions for worker in workers),
                             int(sum(worker.nodes for worker in workers) / 1000 / 1000))

        except ShutdownSoon:
            handler = SignalHandler()

            if any(worker.job for worker in workers):
                logging.info("\n\n### Stopping soon. Press ^C again to abort pending jobs ...\n")

            for worker in workers:
                worker.stop_soon()

            for worker in workers:
                while not worker.finished.wait(0.5):
                    pass
    except (Shutdown, ShutdownSoon):
        if any(worker.job for worker in workers):
            logging.info("\n\n### Good bye! Aborting pending jobs ...\n")
        else:
            logging.info("\n\n### Good bye!")
    except UpdateRequired:
        if any(worker.job for worker in workers):
            logging.info("\n\n### Update required! Aborting pending jobs ...\n")
        else:
            logging.info("\n\n### Update required!")
        raise
    finally:
        handler.ignore = True

        # Stop workers
        for worker in workers:
            worker.stop()

        progress_reporter.stop()

        # Wait
        for worker in workers:
            worker.finished.wait()

    return 0


def cmd_selfplay(args):
    conf = load_conf(args)

    scan_command = validate_scan_command(conf_get(conf, "ScanCommand"), conf)
    if not scan_command:
        raise ConfigError("Ensure you are using Scan 3.0. "
                          "Invalid command: %s" % scan_command)

    print()
    print("### Checking configuration ...")
    print()
    print("Python:           %s (with requests %s)" % (platform.python_version(), requests.__version__))
    print("EngineDir:        %s" % get_engine_dir(conf))
    print("ScanCommand:      %s" % scan_command)
    print("Key:              %s" % (("*" * len(get_key(conf))) or "(none)"))

    cores = validate_cores(conf_get(conf, "Cores"))
    print("Cores:            %d" % cores)

    threads = validate_threads(conf_get(conf, "Threads"), conf)
    instances = 1
    print("Engine processes: %d (each ~%d threads)" % (instances, threads))
    memory = validate_memory(conf_get(conf, "Memory"), conf)
    print("Memory:           %d MB" % memory)
    endpoint = get_endpoint(conf)
    warning = "" if endpoint.startswith("https://") else " (WARNING: not using https)"
    print("Endpoint:         %s%s" % (endpoint, warning))
    print("FixedBackoff:     %s" % parse_bool(conf_get(conf, "FixedBackoff")))
    print()

    if conf.has_section("Scan") and conf.items("Scan"):
        print("Using custom engine options is discouraged:")
        for name, value in conf.items("Scan"):
            if name.lower() == "hash":
                hint = " (use --memory instead)"
            elif name.lower() == "threads":
                hint = " (use --threads-per-process instead)"
            else:
                hint = ""
            print(" * %s = %s%s" % (name, value, hint))
        print()

    print("### Starting workers ...")
    print()

    buckets = [0] * instances
    for i in range(0, cores):
        buckets[i % instances] += 1

    progress_reporter = ProgressReporter(len(buckets) + 4, conf)
    progress_reporter.setDaemon(True)
    progress_reporter.start()

    if hasattr(args, "selfplay_level") and args.selfplay_level is not None:
        level = args.selfplay_level
    else:
        level = 1

    if hasattr(args, "selfplay_games") and args.selfplay_games is not None:
        games = args.selfplay_games
    else:
        games = 200

    workers = [Worker(conf, bucket, memory // instances, progress_reporter, level, games) for bucket in buckets]

    # Start all threads
    for i, worker in enumerate(workers):
        worker.set_name("><> %d" % (i + 1))
        worker.setDaemon(True)
        worker.start()

    # Wait while the workers are running
    try:
        # Let SIGTERM and SIGINT gracefully terminate the program
        handler = SignalHandler()

        try:
            while True:
                # Check worker status
                for _ in range(int(max(1, STAT_INTERVAL / len(workers)))):
                    for worker in workers:
                        if worker.finished.wait(1.0):
                            raise Shutdown

                # Log stats
                logging.info("[draughtsnet v%s] Analyzed %d positions, crunched %d million nodes",
                             __version__,
                             sum(worker.positions for worker in workers),
                             int(sum(worker.nodes for worker in workers) / 1000 / 1000))

        except ShutdownSoon:
            handler = SignalHandler()

            if any(worker.job for worker in workers):
                logging.info("\n\n### Stopping soon. Press ^C again to abort pending jobs ...\n")

            for worker in workers:
                worker.stop_soon()

            for worker in workers:
                while not worker.finished.wait(0.5):
                    pass
    except (Shutdown, ShutdownSoon):
        if any(worker.job for worker in workers):
            logging.info("\n\n### Good bye! Aborting pending jobs ...\n")
        else:
            logging.info("\n\n### Good bye!")
    except UpdateRequired:
        if any(worker.job for worker in workers):
            logging.info("\n\n### Update required! Aborting pending jobs ...\n")
        else:
            logging.info("\n\n### Update required!")
        raise
    finally:
        handler.ignore = True

        # Stop workers
        for worker in workers:
            worker.stop()

        progress_reporter.stop()

        # Wait
        for worker in workers:
            worker.finished.wait()

    return 0


def cmd_configure(args):
    configure(args)
    return 0


def cmd_systemd(args):
    conf = load_conf(args)

    template = textwrap.dedent("""\
        [Unit]
        Description=Draughtsnet instance
        After=network-online.target
        Wants=network-online.target

        [Service]
        ExecStart={start}
        WorkingDirectory={cwd}
        User={user}
        Group={group}
        Nice=5
        CapabilityBoundingSet=
        PrivateTmp=true
        PrivateDevices=true
        DevicePolicy=closed
        ProtectSystem={protect_system}
        NoNewPrivileges=true
        Restart=always

        [Install]
        WantedBy=multi-user.target""")

    # Prepare command line arguments
    builder = [shell_quote(sys.executable)]

    if __package__ is None:
        builder.append(shell_quote(os.path.abspath(sys.argv[0])))
    else:
        builder.append("-m")
        builder.append(shell_quote(os.path.splitext(os.path.basename(__file__))[0]))

    if args.no_conf:
        builder.append("--no-conf")
    else:
        config_file = os.path.abspath(args.conf or DEFAULT_CONFIG)
        builder.append("--conf")
        builder.append(shell_quote(config_file))

    if args.key is not None:
        builder.append("--key")
        builder.append(shell_quote(validate_key(args.key, conf)))
    if args.engine_dir is not None:
        builder.append("--engine-dir")
        builder.append(shell_quote(validate_engine_dir(args.engine_dir)))
    if args.scan_command is not None:
        builder.append("--scan-command")
        builder.append(shell_quote(validate_scan_command(args.scan_command, conf)))
    if args.cores is not None:
        builder.append("--cores")
        builder.append(shell_quote(str(validate_cores(args.cores))))
    if args.memory is not None:
        builder.append("--memory")
        builder.append(shell_quote(str(validate_memory(args.memory, conf))))
    if args.threads is not None:
        builder.append("--threads-per-process")
        builder.append(shell_quote(str(validate_threads(args.threads, conf))))
    if args.endpoint is not None:
        builder.append("--endpoint")
        builder.append(shell_quote(validate_endpoint(args.endpoint)))
    if args.fixed_backoff is not None:
        builder.append("--fixed-backoff" if args.fixed_backoff else "--no-fixed-backoff")
    for option_name, option_value in args.setoption:
        builder.append("--setoption")
        builder.append(shell_quote(option_name))
        builder.append(shell_quote(option_value))

    builder.append("run")

    start = " ".join(builder)

    protect_system = "full"

    print(template.format(
        user=getpass.getuser(),
        group=getpass.getuser(),
        cwd=os.path.abspath("."),
        start=start,
        protect_system=protect_system
    ))

    try:
        if os.geteuid() == 0:
            print("\n# WARNING: Running as root is not recommended!", file=sys.stderr)
    except AttributeError:
        # No os.getuid() on Windows
        pass

    if sys.stdout.isatty():
        print("\n# Example usage:", file=sys.stderr)
        print("# python -m draughtsnet systemd | sudo tee /etc/systemd/system/draughtsnet.service", file=sys.stderr)
        print("# sudo systemctl enable draughtsnet.service", file=sys.stderr)
        print("# sudo systemctl start draughtsnet.service", file=sys.stderr)
        print("#", file=sys.stderr)
        print("# Live view of the log: sudo journalctl --follow -u draughtsnet", file=sys.stderr)


@contextlib.contextmanager
def make_cpuid():
    # Loosely based on cpuid.py by Anders Høst, licensed MIT:
    # https://github.com/flababah/cpuid.py

    # Prepare system information
    is_windows = os.name == "nt"
    is_64bit = ctypes.sizeof(ctypes.c_void_p) == 8
    if platform.machine().lower() not in ["amd64", "x86_64", "x86", "i686"]:
        raise OSError("Got no CPUID opcodes for %s" % platform.machine())

    # Struct for return value
    class CPUID_struct(ctypes.Structure):
        _fields_ = [("eax", ctypes.c_uint32),
                    ("ebx", ctypes.c_uint32),
                    ("ecx", ctypes.c_uint32),
                    ("edx", ctypes.c_uint32)]

    # Select kernel32 or libc
    if is_windows:
        libc = ctypes.windll.kernel32
    else:
        libc = ctypes.cdll.LoadLibrary(None)

    # Select opcodes
    if is_64bit:
        if is_windows:
            # Windows x86_64
            # Three first call registers : RCX, RDX, R8
            # Volatile registers         : RAX, RCX, RDX, R8-11
            opc = [
                0x53,                    # push   %rbx
                0x89, 0xd0,              # mov    %edx,%eax
                0x49, 0x89, 0xc9,        # mov    %rcx,%r9
                0x44, 0x89, 0xc1,        # mov    %r8d,%ecx
                0x0f, 0xa2,              # cpuid
                0x41, 0x89, 0x01,        # mov    %eax,(%r9)
                0x41, 0x89, 0x59, 0x04,  # mov    %ebx,0x4(%r9)
                0x41, 0x89, 0x49, 0x08,  # mov    %ecx,0x8(%r9)
                0x41, 0x89, 0x51, 0x0c,  # mov    %edx,0xc(%r9)
                0x5b,                    # pop    %rbx
                0xc3                     # retq
            ]
        else:
            # Posix x86_64
            # Three first call registers : RDI, RSI, RDX
            # Volatile registers         : RAX, RCX, RDX, RSI, RDI, R8-11
            opc = [
                0x53,                    # push   %rbx
                0x89, 0xf0,              # mov    %esi,%eax
                0x89, 0xd1,              # mov    %edx,%ecx
                0x0f, 0xa2,              # cpuid
                0x89, 0x07,              # mov    %eax,(%rdi)
                0x89, 0x5f, 0x04,        # mov    %ebx,0x4(%rdi)
                0x89, 0x4f, 0x08,        # mov    %ecx,0x8(%rdi)
                0x89, 0x57, 0x0c,        # mov    %edx,0xc(%rdi)
                0x5b,                    # pop    %rbx
                0xc3                     # retq
            ]
    else:
        # CDECL 32 bit
        # Three first call registers : Stack (%esp)
        # Volatile registers         : EAX, ECX, EDX
        opc = [
            0x53,                    # push   %ebx
            0x57,                    # push   %edi
            0x8b, 0x7c, 0x24, 0x0c,  # mov    0xc(%esp),%edi
            0x8b, 0x44, 0x24, 0x10,  # mov    0x10(%esp),%eax
            0x8b, 0x4c, 0x24, 0x14,  # mov    0x14(%esp),%ecx
            0x0f, 0xa2,              # cpuid
            0x89, 0x07,              # mov    %eax,(%edi)
            0x89, 0x5f, 0x04,        # mov    %ebx,0x4(%edi)
            0x89, 0x4f, 0x08,        # mov    %ecx,0x8(%edi)
            0x89, 0x57, 0x0c,        # mov    %edx,0xc(%edi)
            0x5f,                    # pop    %edi
            0x5b,                    # pop    %ebx
            0xc3                     # ret
        ]

    code_size = len(opc)
    code = (ctypes.c_ubyte * code_size)(*opc)

    if is_windows:
        # Allocate executable memory
        libc.VirtualAlloc.restype = ctypes.c_void_p
        libc.VirtualAlloc.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong, ctypes.c_ulong]
        addr = libc.VirtualAlloc(None, code_size, 0x1000, 0x40)
        if not addr:
            raise MemoryError("Could not VirtualAlloc RWX memory")
    else:
        # Allocate memory
        libc.valloc.restype = ctypes.c_void_p
        libc.valloc.argtypes = [ctypes.c_size_t]
        addr = libc.valloc(code_size)
        if not addr:
            raise MemoryError("Could not valloc memory")

        # Make executable
        libc.mprotect.restype = ctypes.c_int
        libc.mprotect.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
        if 0 != libc.mprotect(addr, code_size, 1 | 2 | 4):
            raise OSError("Failed to set RWX using mprotect")

    # Copy code to allocated executable memory. No need to flush instruction
    # cache for CPUID.
    ctypes.memmove(addr, code, code_size)

    # Create and yield callable
    result = CPUID_struct()
    func_type = ctypes.CFUNCTYPE(None, ctypes.POINTER(CPUID_struct), ctypes.c_uint32, ctypes.c_uint32)
    func_ptr = func_type(addr)

    def cpuid(eax, ecx=0):
        func_ptr(result, eax, ecx)
        return result.eax, result.ebx, result.ecx, result.edx

    yield cpuid

    # Free
    if is_windows:
        libc.VirtualFree.restype = ctypes.c_long
        libc.VirtualFree.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_ulong]
        libc.VirtualFree(addr, 0, 0x8000)
    else:
        libc.free.restype = None
        libc.free.argtypes = [ctypes.c_void_p]
        libc.free(addr)


def cmd_cpuid(argv):
    with make_cpuid() as cpuid:
        headers = ["CPUID", "EAX", "EBX", "ECX", "EDX"]
        print(" ".join(header.ljust(8) for header in headers).rstrip())

        for eax in [0x0, 0x80000000]:
            highest, _, _, _ = cpuid(eax)
            for eax in range(eax, highest + 1):
                a, b, c, d = cpuid(eax)
                print("%08x %08x %08x %08x %08x" % (eax, a, b, c, d))


def main(argv):
    # Parse command line arguments
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verbose", "-v", default=0, action="count", help="increase verbosity")
    parser.add_argument("--version", action="version", version="draughtsnet v{0}".format(__version__))

    g = parser.add_argument_group("configuration")
    g.add_argument("--conf", help="configuration file")
    g.add_argument("--no-conf", action="store_true", help="do not use a configuration file")
    g.add_argument("--key", "--apikey", "-k", help="draughtsnet api key")

    g = parser.add_argument_group("resources")
    g.add_argument("--cores", help="number of cores to use for engine processes (or auto for n - 1, or all for n)")
    g.add_argument("--memory", help="total memory (MB) to use for engine hashtables")

    g = parser.add_argument_group("advanced")
    g.add_argument("--endpoint", help="lidraughts http endpoint (default: %s)" % DEFAULT_ENDPOINT)
    g.add_argument("--engine-dir", help="engine working directory")
    g.add_argument("--scan-command", help="scan hub-mode command")
    g.add_argument("--threads-per-process", "--threads", type=int, dest="threads", help="hint for the number of threads to use per engine process (default: %d)" % DEFAULT_THREADS)
    g.add_argument("--fixed-backoff", action="store_true", default=None, help="fixed backoff (only recommended for move servers)")
    g.add_argument("--no-fixed-backoff", dest="fixed_backoff", action="store_false", default=None)
    g.add_argument("--setoption", "-o", nargs=2, action="append", default=[], metavar=("NAME", "VALUE"), help="set a custom uci option")

    g.add_argument("--selfplay-games", type=int, help="amount of games to play against self (default: 200)")
    g.add_argument("--selfplay-level", type=int, help="selfplay engine level 1-8 (default: 1)")

    commands = collections.OrderedDict([
        ("run", cmd_run),
        ("configure", cmd_configure),
        ("systemd", cmd_systemd),
        ("cpuid", cmd_cpuid),
        ("selfplay", cmd_selfplay),
    ])

    parser.add_argument("command", default="run", nargs="?", choices=commands.keys())

    args = parser.parse_args(argv[1:])

    # Setup logging
    setup_logging(args.verbose,
                  sys.stderr if args.command == "systemd" else sys.stdout)

    # Show intro
    if args.command not in ["systemd", "cpuid"]:
        print(intro())
        sys.stdout.flush()

    # Run
    try:
        sys.exit(commands[args.command](args))
    except UpdateRequired:
        logging.error("Update required. Exiting (status 70)")
        return 70
    except ConfigError:
        logging.exception("Configuration error")
        return 78
    except (KeyboardInterrupt, Shutdown, ShutdownSoon):
        return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
