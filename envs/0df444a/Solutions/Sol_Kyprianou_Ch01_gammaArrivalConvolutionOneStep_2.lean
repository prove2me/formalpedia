-- Prove2me | solution 2 for Kyprianou.Ch01.gammaArrivalConvolutionOneStep
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:21:38.693972+00:00
-- url     : https://prove2.me/submissions/1db3d66e-8688-403e-97fd-dc19aa415766

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
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (z : ℝ) :
    (∫⁻ x : ℝ, LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x)) =
      LevyFoundations.arrivalGammaDensity beta (n + 1) z := by
  exact levy_foundations_arrivalGammaDensityConvolution hbeta n z
