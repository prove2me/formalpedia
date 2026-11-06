-- Prove2me | solution 1 for Given.stAlgorithm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:09:44.041207+00:00
-- url     : https://prove2.me/submissions/738b5632-c7dc-4ae8-97c8-13cf3a565a34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_stCountCost
import Theorems.Thm_Exits_stCountCost
import Theorems.Thm_Printed_stAlgorithm_of
import Theorems.Thm_Printed_stCountCost
import Theorems.Thm_Suffices_stSuffices


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : StAlgorithm := stAlgorithm_of Suffices.stSuffices stCountCost
end Given
