-- Prove2me | solution 1 for Given.stFormulaGiven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:00:51.000819+00:00
-- url     : https://prove2.me/submissions/34d307c4-89db-4400-a9de-25d019c05298

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
import Theorems.Thm_Given_ofProcs_poly
import Theorems.Thm_Eight_ViaGrouping_satProcs_keepsP
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Printed_formulaProcs_keeps
import Theorems.Thm_Printed_formula_isNetwork
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}
namespace Given
theorem _root_.solution : StFormulaGiven := fun g hg k Φ =>
  ⟨formula_isNetwork hg k Φ, ofProcs_poly _ (formulaProcs_keeps g k) (satProcs_keepsP g k).P (Unary.const 1)⟩
end Given
