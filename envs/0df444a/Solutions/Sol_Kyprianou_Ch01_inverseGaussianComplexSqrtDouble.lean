-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianComplexSqrtDouble
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:51:34.195382+00:00
-- url     : https://prove2.me/submissions/bfa470d8-68f4-41b8-abf9-804979ccb81f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex Real Set
open ComplexOrder
set_option autoImplicit false

theorem solution (z : ℂ) (hz : z ≠ 0) :
    Complex.sqrt ((2 : ℂ) * z) =
      ((Real.sqrt 2 : ℝ) : ℂ) * Complex.sqrt z := by
  have hTwo : Complex.exp (Complex.log (2 : ℂ) / 2) =
      ((Real.sqrt 2 : ℝ) : ℂ) := by
    have hNonneg : (0 : ℂ) ≤ 2 := by norm_num
    have hRoot : Complex.sqrt (2 : ℂ) =
        ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [Complex.sqrt_of_nonneg hNonneg]
      norm_num
    rw [← hRoot]
    exact (sqrt_eq_exp (z := (2 : ℂ)) (by norm_num)).symm
  have hprod : ((2 : ℂ) * z) ≠ 0 := mul_ne_zero (by norm_num) hz
  rw [sqrt_eq_exp hprod, sqrt_eq_exp hz]
  have hmul : Complex.log ((2 : ℂ) * z) =
      ((Real.log (2 : ℝ) : ℝ) : ℂ) + Complex.log z := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.log_ofReal_mul (by norm_num : 0 < (2 : ℝ)) hz)
  rw [hmul]
  have hlog : ((Real.log (2 : ℝ) : ℝ) : ℂ) =
      Complex.log (2 : ℂ) := Complex.ofReal_log (by norm_num)
  rw [hlog, add_div, Complex.exp_add, hTwo]
