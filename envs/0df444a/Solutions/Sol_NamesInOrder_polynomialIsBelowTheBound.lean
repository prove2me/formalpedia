-- Prove2me | solution 1 for NamesInOrder.polynomialIsBelowTheBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:37.272498+00:00
-- url     : https://prove2.me/submissions/ca9d565c-1259-427a-a425-013341cd177b

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
import Theorems.Thm_NamesInOrder_polynomialIsBelowTheBoundInN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_MinOfBounds_min_time_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : PolynomialIsBelowTheBound := by
  intro c
  obtain ⟨c₁, h₁⟩ := polynomialIsBelowTheBoundInM c
  obtain ⟨c₂, h₂⟩ := polynomialIsBelowTheBoundInN c
  refine ⟨max c₁ c₂, fun k n φ hk hφ hm hn ho => ?_⟩
  obtain ⟨-, hs, hp⟩ := codeIsShort k n φ hk (by omega) hφ
  have a₁ : c * (SatM.enc k φ).length ^ c ≤ timeM c₁ k φ.length := (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (hs ho) c)).trans (h₁ k φ.length hk hm)
  have a₂ : c * (SatM.enc k φ).length ^ c ≤ timeN c₂ k n := (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hp c)).trans (h₂ k n hk hn)
  exact Nat.le_floor (((Nat.cast_le (α := ℝ)).2 (le_min a₁ a₂)).trans (min_time_le c₁ c₂ hk hm hn))
end NamesInOrder
