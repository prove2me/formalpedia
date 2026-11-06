-- Prove2me | solution 1 for Given.stClique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:50:15.231195+00:00
-- url     : https://prove2.me/submissions/1e2f8e73-e66a-4dbc-85cf-aa20fb30beee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_stLevelPoly
import Theorems.Thm_Given_stLevelTied
import Theorems.Thm_Printed_stBrute
import Theorems.Thm_Printed_stClique_of
import Theorems.Thm_Printed_stLevelPoly
import Theorems.Thm_Printed_stLevelTied


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : StClique := stClique_of stBrute stLevelTied stLevelPoly
end Given
