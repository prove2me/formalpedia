-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_exp_increment_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:45:24.671151+00:00
-- url     : https://prove2.me/submissions/18454447-7def-4aa2-82fd-30f04bc1aa06

import Mathlib
set_option autoImplicit false

/-- A global first-order bound with a real-part cap, using the
quadratic small-increment bound and the elementary large-increment bound. -/
theorem solution (z : Complex) (K : Real) (hK : 0 ≤ K)
    (hre : (-z).re ≤ K) :
    ‖1-Complex.exp (-z)‖ ≤ 2*Real.exp K*‖z‖ := by
  have hE : 1 ≤ Real.exp K := Real.one_le_exp_iff.mpr hK
  by_cases hs : ‖z‖ ≤ 1
  · have h := Complex.norm_exp_sub_one_le (x := -z) (by simpa using hs)
    rw [norm_sub_rev]
    calc
      _ ≤ 2*‖z‖ := by simpa using h
      _ ≤ 2*Real.exp K*‖z‖ := by
        gcongr
        linarith
  · calc
      _ ≤ ‖(1:Complex)‖+‖Complex.exp (-z)‖ := norm_sub_le _ _
      _ ≤ 2*Real.exp K := by
        rw [norm_one,Complex.norm_exp]
        linarith [Real.exp_le_exp.mpr hre]
      _ ≤ 2*Real.exp K*‖z‖ := by
        have h : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hs)
        nlinarith [mul_nonneg (Real.exp_pos K).le (sub_nonneg.mpr h)]
