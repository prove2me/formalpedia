-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneFiniteIntervalCompensatedIBP
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:07:08.834174+00:00
-- url     : https://prove2.me/submissions/aa635acb-7da9-48de-aa14-8b0ec8b39081

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneComplexProductIBP
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha a c : ℝ) (ha : 1 < alpha) (hb : alpha < 2)
    (hapos : 0 < a) (hac : a < c) :
    (∫ r in a..c,
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
            Complex.I * (r : ℂ)) *
          (((r ^ (-(alpha + 1) : ℝ) : ℝ)) : ℂ)) =
      (Complex.exp (Complex.I * (a : ℂ)) - 1 -
          Complex.I * (a : ℂ)) *
        (((a ^ (-alpha) : ℝ)) : ℂ) / (alpha : ℂ) -
      (Complex.exp (Complex.I * (c : ℂ)) - 1 -
          Complex.I * (c : ℂ)) *
        (((c ^ (-alpha) : ℝ)) : ℂ) / (alpha : ℂ) +
      (Complex.I / (alpha : ℂ)) *
        (∫ r in a..c,
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (-alpha) : ℝ)) : ℂ)) := by
  have hα : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one ha))
  have hpt (r : ℝ) :
      (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) =
      (-(Complex.I / (alpha : ℂ))) *
        ((Complex.exp (Complex.I * (r : ℂ)) - 1) *
          (((r ^ (-alpha) : ℝ)) : ℂ)) := by
    push_cast
    field_simp [hα]
  have hint :
      (∫ r in a..c,
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ)) =
      (-(Complex.I / (alpha : ℂ))) *
        (∫ r in a..c,
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (-alpha) : ℝ)) : ℂ)) := by
    simp_rw [hpt]
    exact intervalIntegral.integral_const_mul
      (-(Complex.I / (alpha : ℂ)))
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1) *
          (((r ^ (-alpha) : ℝ)) : ℂ))
  rw [Kyprianou.Ch01.stableAlphaAboveOneComplexProductIBP
    alpha a c ha hb hapos hac, hint]
  push_cast
  field_simp [hα]
  try ring
