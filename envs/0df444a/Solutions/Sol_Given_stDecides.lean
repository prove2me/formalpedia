-- Prove2me | solution 1 for Given.stDecides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:15:05.85667+00:00
-- url     : https://prove2.me/submissions/be2516cd-422a-4af2-8231-838718a70f83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_stAlgorithm
import Theorems.Thm_Enumerate_stEnumeration
import Theorems.Thm_Exits_stAlgorithm
import Theorems.Thm_Printed_stAlgorithm
import Theorems.Thm_Printed_stDecides_of


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : StDecides := stDecides_of stAlgorithm Enumerate.stEnumeration
end Given
