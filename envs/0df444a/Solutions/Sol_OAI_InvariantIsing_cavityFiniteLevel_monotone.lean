-- Prove2me | solution 1 for OAI.InvariantIsing.cavityFiniteLevel_monotone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:25.425472+00:00
-- url     : https://prove2.me/submissions/1d53bc24-9a90-4a97-a6cd-3a7b940ebca6

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAIQ258001

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

lemma cavityFiniteLevel_monotone_oai (n : ℕ) : Monotone (cavityFiniteLevel n) := by
  intro i j hij
  exact min_le_min_right n hij

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavityFiniteLevel_monotone_oai := @OAI.InvariantIsing.cavityFiniteLevel_monotone_oai
