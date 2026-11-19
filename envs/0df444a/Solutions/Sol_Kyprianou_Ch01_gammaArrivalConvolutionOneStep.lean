-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalConvolutionOneStep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:35:43.918032+00:00
-- url     : https://prove2.me/submissions/048cb823-354d-4ad5-9975-b28f6b4c2c4d

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionNonnegative
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionNegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution (beta : ℝ) (hbeta : 0 < beta)
    (n : ℕ) (z : ℝ) :
    (∫⁻ x : ℝ, LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x)) =
      LevyFoundations.arrivalGammaDensity beta (n + 1) z := by
  by_cases hz : 0 ≤ z
  · exact Kyprianou.Ch01.gammaArrivalConvolutionNonnegative beta hbeta n z hz
  · have hneg : z < 0 := lt_of_not_ge hz
    rw [Kyprianou.Ch01.gammaArrivalConvolutionNegative beta hbeta n z hneg]
    unfold LevyFoundations.arrivalGammaDensity
    rw [Set.indicator_of_notMem (show z ∉ Set.Ici (0 : ℝ) from
      not_le.mpr hneg)]
