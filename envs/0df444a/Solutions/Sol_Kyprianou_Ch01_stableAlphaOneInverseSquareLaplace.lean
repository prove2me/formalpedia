-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneInverseSquareLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:18:34.31502+00:00
-- url     : https://prove2.me/submissions/fd1760be-f2e7-4b05-98bf-a7af2d9e5f2d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
set_option autoImplicit false
/-! The inverse square is the positive Laplace integral of t. -/
theorem solution
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-(x * t))) =
      (x ^ 2)⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := x) (by norm_num) hx
  simpa [show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, Real.Gamma_two, one_div, inv_pow] using h
