-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalConvolutionNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:21:39.45687+00:00
-- url     : https://prove2.me/submissions/12b4f9f9-7a59-434f-bcb6-705e1297ac85

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_levy_foundations_arrivalGammaDensityConvolution
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
theorem solution
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ x : ℝ, LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x)) = LevyFoundations.arrivalGammaDensity beta (n + 1) z := by
  exact levy_foundations_arrivalGammaDensityConvolution hbeta n z
