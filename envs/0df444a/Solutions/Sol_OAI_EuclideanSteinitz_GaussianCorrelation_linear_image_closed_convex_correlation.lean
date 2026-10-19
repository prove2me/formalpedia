-- Prove2me | solution 1 for OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:19:01.871474+00:00
-- url     : https://prove2.me/submissions/a9741f1d-787d-4b5b-82b0-c9ab8ab05550

import Mathlib
import Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_stdGaussian_closed_convex_correlation

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Correlation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian correlation and symmetric convex events. -/

section

namespace EuclideanSteinitz.GaussianCorrelation
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma linear_image_closed_convex_correlation_oai (A : E →L[ℝ] F) {K L : Set F}
    (hK : IsClosed K) (hL : IsClosed L) (hcK : Convex ℝ K) (hcL : Convex ℝ L)
    (hsK : ∀ x ∈ K, -x ∈ K) (hsL : ∀ x ∈ L, -x ∈ L) :
    ((stdGaussian E).map A).real K * ((stdGaussian E).map A).real L ≤
      ((stdGaussian E).map A).real (K ∩ L) := by
  simp only [Measure.real, Measure.map_apply A.continuous.measurable hK.measurableSet,
    Measure.map_apply A.continuous.measurable hL.measurableSet,
    Measure.map_apply A.continuous.measurable (hK.inter hL).measurableSet,
    Set.preimage_inter]
  apply stdGaussian_closed_convex_correlation
    (hK.preimage A.continuous) (hL.preimage A.continuous)
    (hcK.linear_preimage A.toLinearMap) (hcL.linear_preimage A.toLinearMap)
  · intro x hx
    simpa using hsK (A x) hx
  · intro x hx
    simpa using hsL (A x) hx

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation_oai.{u_1, u_2} := @OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation_oai.{u_1, u_2}
