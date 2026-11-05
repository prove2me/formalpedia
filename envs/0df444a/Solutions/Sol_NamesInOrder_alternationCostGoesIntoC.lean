-- Prove2me | solution 1 for NamesInOrder.alternationCostGoesIntoC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:22.038221+00:00
-- url     : https://prove2.me/submissions/a5cbecce-c82f-4a62-a0e8-45c9949a98af

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
import Theorems.Thm_NamesInOrder_two_le_min
import Theorems.Thm_NamesInOrder_polynomialIsBelowTheBound
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_MinOfBounds_min_time_le
import Theorems.Thm_PairsToBound_choice_le
import Theorems.Thm_PairsToBound_two_rpow_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)
namespace NamesInOrder
theorem _root_.solution : AlternationCostGoesIntoC := by
  intro C₁ C₂ q
  obtain ⟨c', hc'⟩ := polynomialIsBelowTheBound 1
  refine ⟨q * (max (max C₁ C₂) (c' + 1) + 2), fun k n φ hk hφ hm hn ho => ?_⟩
  have hX := two_le_min (n := n) hk hm hn
  have hX0 : 0 ≤ min (expM k φ.length) (expN k n) := by linarith
  have ht := (min_time_le C₁ C₂ hk hm hn).trans (two_rpow_mono (le_max_left (max C₁ C₂) (c' + 1)) hX0)
  have hL : ((SatM.enc k φ).length : ℝ) ≤ (2 : ℝ) ^ ((c' : ℝ) * min (expM k φ.length) (expN k n)) := by
    have h1 : (SatM.enc k φ).length ≤ timeMin c' k φ.length n := by
      have := hc' k n φ hk hφ hm hn ho
      rwa [one_mul, pow_one] at this
    exact ((Nat.cast_le (α := ℝ)).2 h1).trans (Nat.floor_le (by positivity))
  have hl : (((SatM.enc k φ).length + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max (max C₁ C₂) (c' + 1) : ℕ) : ℝ) * min (expM k φ.length) (expN k n)) := by
    refine le_trans ?_ (two_rpow_mono (le_max_right (max C₁ C₂) (c' + 1)) hX0)
    have e : (2 : ℝ) ^ (((c' + 1 : ℕ) : ℝ) * min (expM k φ.length) (expN k n)) = (2 : ℝ) ^ ((c' : ℝ) * min (expM k φ.length) (expN k n)) * (2 : ℝ) ^ min (expM k φ.length) (expN k n) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ min (expM k φ.length) (expN k n) := by
      have := Real.rpow_le_rpow_of_exponent_le one_le_two (show (1 : ℝ) ≤ min (expM k φ.length) (expN k n) by linarith)
      rwa [Real.rpow_one] at this
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((c' : ℝ) * min (expM k φ.length) (expN k n)) := Real.one_le_rpow one_le_two (mul_nonneg (Nat.cast_nonneg c') hX0)
    have h3 := mul_le_mul_of_nonneg_left h2 (zero_le_one.trans h1)
    rw [e, Nat.cast_add, Nat.cast_one]
    linarith
  exact choice_le q (max (max C₁ C₂) (c' + 1)) (by linarith) ht hl
end NamesInOrder
