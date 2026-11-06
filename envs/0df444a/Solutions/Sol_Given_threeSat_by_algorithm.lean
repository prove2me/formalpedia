-- Prove2me | solution 1 for Given.threeSat_by_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:21:00.987291+00:00
-- url     : https://prove2.me/submissions/a1703596-8978-4338-aaf2-148b4b3490c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_stDecides
import Theorems.Thm_Exits_stDecides
import Theorems.Thm_Printed_stDecides
import Theorems.Thm_Printed_threeSat_by_algorithm_of


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : Sat3.ThmEveryDelta := threeSat_by_algorithm_of stDecides
end Given
