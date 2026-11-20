-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianWeightedFourierGammaIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:42:09.006189+00:00
-- url     : https://prove2.me/submissions/66e3a54b-cb31-4bd5-9e85-03759834bc48

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFourierWithDensity
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpGammaDifference
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaRootNormalisation
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      (ENNReal.ofReal
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2)))).toReal •
      ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) =
      Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
        2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  have hW := Kyprianou.Ch01.inverseGaussianFourierWithDensity b hb theta
  have hG := Kyprianou.Ch01.inverseGaussianJumpGammaDifference b hb theta
  have hR := Kyprianou.Ch01.inverseGaussianGammaRootNormalisation b hb theta
  have hF :
      (∫ x in Set.Ioi (0 : ℝ),
        (ENNReal.ofReal
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2)))).toReal •
        ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) =
      (∫ x in Set.Ioi (0 : ℝ),
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2))) •
        ((1 : ℂ) -
          Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hp : 0 ≤ (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) := by positivity
    simp only [ENNReal.toReal_ofReal hp]
  exact hF.trans (hW.symm.trans (hG.trans hR))
