-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_exp_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:25.59911+00:00
-- url     : https://prove2.me/submissions/1b4338cf-f16a-4aca-9373-e461d52ab6c9

import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false

/-- Quadratic error in the small complex exponential increment. -/
theorem solution (z : Complex) (hz : ‖z‖ ≤ 1) :
    ‖1 - Complex.exp (-z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by simpa using hz)
  have hEq : 1 - Complex.exp (-z) - z =
      -(Complex.exp (-z) - 1 - (-z)) := by ring
  rw [hEq, norm_neg]
  simpa using h
