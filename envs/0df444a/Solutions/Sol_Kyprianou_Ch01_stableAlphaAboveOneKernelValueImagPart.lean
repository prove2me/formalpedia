-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneKernelValueImagPart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:20:56.13808+00:00
-- url     : https://prove2.me/submissions/89136fd1-e313-4874-88c8-c762680e6833

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
      ∂volume).im =
      (((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))).im := by
  exact congrArg Complex.im 
    (Kyprianou.Ch01.stableAlphaAboveOneKernelValue alpha ha1 ha2)
