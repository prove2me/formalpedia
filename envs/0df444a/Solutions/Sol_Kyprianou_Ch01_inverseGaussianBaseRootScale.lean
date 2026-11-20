-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianBaseRootScale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:53:44.0163+00:00
-- url     : https://prove2.me/submissions/9189e554-8fcb-46cb-8d2d-239a0646a577

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex Real ComplexOrder
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    Real.sqrt 2 * Real.sqrt (b ^ 2 / 2) = b := by
  calc
    Real.sqrt 2 * Real.sqrt (b ^ 2 / 2) =
      Real.sqrt (2 * (b ^ 2 / 2)) :=
        (Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) _).symm
    _ = Real.sqrt (b ^ 2) := by congr 1; ring
    _ = |b| := Real.sqrt_sq_eq_abs b
    _ = b := abs_of_pos hb
