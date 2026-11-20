-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneKernelValueRealPart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:21:06.345411+00:00
-- url     : https://prove2.me/submissions/bb8ac3b5-614b-4aa2-8398-469f4f3208fb

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValue
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume).re =
      (((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))).re := by
  exact congrArg Complex.re 
    (Kyprianou.Ch01.stableAlphaAboveOneKernelValue alpha ha1 ha2)
