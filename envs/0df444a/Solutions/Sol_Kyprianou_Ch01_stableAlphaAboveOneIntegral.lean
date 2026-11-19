-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneIntegral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:16:03.764878+00:00
-- url     : https://prove2.me/submissions/a8ddb258-6fd1-4148-86a3-d4c85fc64cdd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
        ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ))) := by
  exact ⟨Kyprianou.Ch01.stableAlphaAboveOneKernelIntegrable
    alpha ha1 ha2,
    Kyprianou.Ch01.stableAlphaAboveOneKernelValue alpha ha1 ha2⟩
