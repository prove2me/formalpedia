-- Prove2me | solution 1 for MinOfBounds.min_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:39:10.205924+00:00
-- url     : https://prove2.me/submissions/afa3300e-5201-4ecf-8e35-ad790562cdb6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_MinOfBounds_Arith
import Theorems.Thm_VariableBound_Paper_two_le_expM
import Theorems.Thm_VariableBound_Paper_two_le_expN


set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution (C₁ C₂ : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max C₁ C₂ : ℕ) : ℝ) * min (expM k m) (expN k n)) := by
  have hM := two_le_expM hk hm
  have hN := two_le_expN hk hn
  rcases le_total (expM k m) (expN k n) with h | h
  · rw [min_eq_left h]
    calc ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (timeM C₁ k m : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ (2 : ℝ) ^ ((C₁ : ℝ) * expM k m) := Nat.floor_le (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left _ _) (by linarith))
  · rw [min_eq_right h]
    calc ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (timeN C₂ k n : ℝ) := by exact_mod_cast min_le_right _ _
      _ ≤ (2 : ℝ) ^ ((C₂ : ℝ) * expN k n) := Nat.floor_le (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right _ _) (by linarith))
end MinOfBounds
