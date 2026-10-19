-- Prove2me | solution 1 for OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:19:02.790648+00:00
-- url     : https://prove2.me/submissions/71cb2b2f-e614-4351-99e6-a68cb7f57fb5

import Mathlib
import Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_linear_image_closed_convex_correlation

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

lemma linear_image_finite_correlation_oai {ι : Type*} (A : E →L[ℝ] F)
    (s : Finset ι) (K : ι → Set F)
    (hK : ∀ i ∈ s, IsClosed (K i)) (hcK : ∀ i ∈ s, Convex ℝ (K i))
    (hsK : ∀ i ∈ s, ∀ x ∈ K i, -x ∈ K i) :
    ∏ i ∈ s, ((stdGaussian E).map A).real (K i) ≤
      ((stdGaussian E).map A).real (⋂ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ih' := ih (fun i hi => hK i (Finset.mem_insert_of_mem hi))
      (fun i hi => hcK i (Finset.mem_insert_of_mem hi))
      (fun i hi => hsK i (Finset.mem_insert_of_mem hi))
    apply (mul_le_mul_of_nonneg_left ih' (measureReal_nonneg)).trans
    have he := linear_image_closed_convex_correlation A
      (hK a (Finset.mem_insert_self _ _))
      (isClosed_iInter fun i => isClosed_iInter fun hi => hK i (Finset.mem_insert_of_mem hi))
      (hcK a (Finset.mem_insert_self _ _))
      (convex_iInter fun i => convex_iInter fun hi => hcK i (Finset.mem_insert_of_mem hi))
      (hsK a (Finset.mem_insert_self _ _))
      (fun x hx => by
        simp only [Set.mem_iInter] at hx ⊢
        exact fun i hi => hsK i (Finset.mem_insert_of_mem hi) x (hx i hi))
    simpa only [Finset.set_biInter_insert] using he

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation_oai.{u_1, u_2, u_3} := @OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation_oai.{u_1, u_2, u_3}
