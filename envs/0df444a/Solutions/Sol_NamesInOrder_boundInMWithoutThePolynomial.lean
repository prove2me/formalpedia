-- Prove2me | solution 1 for NamesInOrder.boundInMWithoutThePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:42.465989+00:00
-- url     : https://prove2.me/submissions/9e597a1d-08d1-48bf-8548-97b79d902f47

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
import Theorems.Thm_NamesInOrder_codeIsShort
import Theorems.Thm_NamesInOrder_polynomialIsBelowTheBoundInM
import Theorems.Thm_NamesInOrder_timeM_add_timeM_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_clauseCount
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : BoundInMWithoutThePolynomial := by
  intro M C h
  obtain ⟨c', hc'⟩ := polynomialIsBelowTheBoundInM C
  refine ⟨max C c' + 1, fun k n φ hk hφ hm ho => ?_⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := clauseCount k 0 φ hφ
      rw [Nat.mul_zero, Nat.zero_add, one_pow] at this
      omega
    · exact h0
  obtain ⟨-, hs, -⟩ := codeIsShort k n φ hk hn hφ
  obtain ⟨ev⟩ := h k n φ hk hφ hm ho
  have a₁ : C * (SatM.enc k φ).length ^ C ≤ timeM c' k φ.length := (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hs ho) C)).trans (hc' k φ.length hk hm)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ((Nat.add_le_add_left a₁ _).trans (timeM_add_timeM_le C c' hk hm))⟩⟩
end NamesInOrder
