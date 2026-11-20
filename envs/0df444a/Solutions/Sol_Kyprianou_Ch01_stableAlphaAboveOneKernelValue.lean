-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneKernelValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:55:12.267513+00:00
-- url     : https://prove2.me/submissions/6041f9b8-e3f4-4b24-a724-652418071dad

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValueRealPart
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValueImagPart
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ))) := by
  apply Complex.ext
  · exact Kyprianou.Ch01.stableAlphaAboveOneKernelValueRealPart
      alpha ha1 ha2
  · exact Kyprianou.Ch01.stableAlphaAboveOneKernelValueImagPart
      alpha ha1 ha2
