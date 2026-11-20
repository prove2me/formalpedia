-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianBaseHalfPower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:41:37.860269+00:00
-- url     : https://prove2.me/submissions/74b89c30-2f9f-4f11-86bf-8860626da6c0

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_complexHalfLogPrincipalSqrt
open Complex Real ComplexOrder
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    Complex.exp (((1 / 2 : ℝ) : ℂ) *
        Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) =
      ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) := by
  have hbase : (((b ^ 2 / 2 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hrealpos : 0 ≤ (b ^ 2 / 2 : ℝ) :=
    div_nonneg (sq_nonneg b) (by norm_num)
  have hpos : 0 ≤ (((b ^ 2 / 2 : ℝ) : ℂ)) :=
    RCLike.ofReal_nonneg.mpr hrealpos
  calc
    Complex.exp (((1 / 2 : ℝ) : ℂ) *
        Complex.log (((b ^ 2 / 2 : ℝ) : ℂ))) =
      Complex.sqrt (((b ^ 2 / 2 : ℝ) : ℂ)) :=
        Kyprianou.Ch01.complexHalfLogPrincipalSqrt _ hbase
    _ = ((Real.sqrt (b ^ 2 / 2) : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_re] using
        (Complex.sqrt_of_nonneg hpos)
