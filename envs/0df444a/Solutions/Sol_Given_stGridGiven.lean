-- Prove2me | solution 1 for Given.stGridGiven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:39.816914+00:00
-- url     : https://prove2.me/submissions/994c61ce-cf77-41a2-9f4d-7c58c5a4621c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
import Theorems.Thm_Given_gridProcs_poly
import Theorems.Thm_Printed_grid_isNetwork_of
import Theorems.Thm_Printed_stAskServes


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}
namespace Given
theorem _root_.solution : StGridGiven := by
  intro g hg
  obtain ⟨a, ha⟩ := grid_isNetwork_of stAskServes g hg
  exact ⟨a, fun tr c lam B W y h1 h2 h3 h4 h5 => ⟨ha tr c lam B W y h1 h2 h3 h4 h5, gridProcs_poly g tr⟩⟩
end Given
