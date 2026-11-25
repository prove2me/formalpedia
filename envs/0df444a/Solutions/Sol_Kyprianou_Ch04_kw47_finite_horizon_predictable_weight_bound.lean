-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_finite_horizon_predictable_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:10:13.197795+00:00
-- url     : https://prove2.me/submissions/ecb51308-3879-47db-8fab-3bc25a58c514

import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false

/-- The continuous supremum factor bounds predictable Esscher grid weights on a finite horizon. -/
theorem solution (alpha psi u r T : Real)
    (hAlpha : 0 ≤ alpha) (hU : 0 ≤ u)
    (hr : 0 ≤ r) (hrT : r ≤ T) :
    Real.exp (-alpha * u + psi * r) ≤ Real.exp (|psi| * T) := by
  apply Real.exp_le_exp.mpr
  calc
    -alpha * u + psi * r ≤ psi * r := by
      nlinarith [mul_nonneg hAlpha hU]
    _ ≤ |psi| * r := mul_le_mul_of_nonneg_right (le_abs_self psi) hr
    _ ≤ |psi| * T := mul_le_mul_of_nonneg_left hrT (abs_nonneg psi)
