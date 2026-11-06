-- Prove2me | solution 1 for OAI.SevenEighths.ProbeLocal.inv_one_sub_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:15.427639+00:00
-- url     : https://prove2.me/submissions/9d571b2e-fbd7-4223-b459-2a98d23ce0a5

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
set_option autoImplicit false
noncomputable section

theorem solution (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have h : (1 : ℝ) - ‖a‖ ≤ ‖1 - a‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) a
  have h' : (1 / 2 : ℝ) ≤ ‖1 - a‖ := by linarith
  rw [norm_inv]
  calc
    ‖1 - a‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
      apply (inv_le_inv₀ (lt_of_lt_of_le (by norm_num) h') (by norm_num)).2
      exact h'
    _ = 2 := by norm_num
