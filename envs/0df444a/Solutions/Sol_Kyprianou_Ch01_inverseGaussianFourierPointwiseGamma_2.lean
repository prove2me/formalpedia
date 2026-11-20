-- Prove2me | solution 2 for Kyprianou.Ch01.inverseGaussianFourierPointwiseGamma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:52:38.445069+00:00
-- url     : https://prove2.me/submissions/58f5b06c-d711-4071-9f01-73201a9834d3

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerIdentity
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierExpDifference
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierScalarAssocTyped
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution (b theta r : ℝ) (hr : 0 < r) :
    ((1 / Real.sqrt (2 * Real.pi * r ^ 3)) *
      Real.exp (-(b ^ 2 * r / 2))) • ((1 : ℂ) -
      Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ))) = ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      ((Complex.exp (((-(b ^ 2 / 2) : ℝ) : ℂ) * (r : ℂ)) -
        Complex.exp ((((-(b ^ 2 / 2) : ℝ) : ℂ) + Complex.I * (theta : ℂ)) * (r : ℂ))) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hd := Kyprianou.Ch01.inverseGaussianDensityPowerIdentity r hr
  have he := Kyprianou.Ch01.inverseGaussianFourierExpDifference b theta r
  rw [hd]
  calc
    (((1 / Real.sqrt (2 * Real.pi)) * r ^ (-(3 / 2 : ℝ))) *
        Real.exp (-(b ^ 2 * r / 2))) •
        ((1 : ℂ) - Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ))) =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        ((((1 : ℂ) - Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ))) *
          ((Real.exp (-(b ^ 2 * r / 2)) : ℝ) : ℂ)) *
          ((r ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) :=
        Kyprianou.Ch01.inverseGaussianFourierScalarAssocTyped
          (1 / Real.sqrt (2 * Real.pi)) (r ^ (-(3 / 2 : ℝ)))
          (Real.exp (-(b ^ 2 * r / 2)))
          ((1 : ℂ) - Complex.exp (Complex.I * ((theta * r : ℝ) : ℂ)))
    _ = _ := by rw [he]
