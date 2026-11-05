-- Prove2me | solution 1 for NamesInOrder.codeIsShort
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:15.318722+00:00
-- url     : https://prove2.me/submissions/09d5f0c7-acb7-4b0a-97af-21846dc0995a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_NamesInOrder_Arith
import Theorems.Thm_NamesInOrder_variablesAreFew
import Theorems.Thm_NamesInOrder_length_le_sq
import Theorems.Thm_NamesInOrder_length_le_pow
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : CodeIsShort := by
  intro k n φ hk hn hφ
  refine ⟨ClauseBound.Alg.End.length_enc k φ, fun ho => ?_, length_le_pow hk hn hφ⟩
  have hm : 1 ≤ φ.length := by
    have := variablesAreFew k n φ hφ ho
    rcases Nat.eq_zero_or_pos φ.length with h0 | h0
    · rw [h0] at this
      omega
    · exact h0
  exact length_le_sq hk hm hφ ho
end NamesInOrder
