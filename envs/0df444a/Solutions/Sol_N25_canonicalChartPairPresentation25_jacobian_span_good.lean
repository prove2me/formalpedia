-- Prove2me | solution 1 for N25.canonicalChartPairPresentation25_jacobian_span_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:54.865943+00:00
-- url     : https://prove2.me/submissions/4e6280bc-6078-4f3f-8262-0fbe7b28f1ee

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Theorems.Thm_N25_canonicalChartJacobianIdeal25_eq_top_good
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_canonicalChartPairPresentation25_jacobian

/-! Smooth canonical charts, with relative dimension one from their literal presentations. -/
noncomputable section

namespace N25

/-- The Jacobians of the selected finite presentations span the unit ideal. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (pivot : Fin 4) :
    Ideal.span (Set.range fun pair : CanonicalChartColumnPair25 pivot =>
      (canonicalChartPairPresentation25 K pivot pair).jacobian) = ⊤ := by
  apply top_unique
  rw [← canonicalChartJacobianIdeal25_eq_top_good p hp K pivot]
  apply Ideal.span_le.mpr
  rintro m ⟨j, k, hj, hk, hjk, rfl⟩
  rw [← canonicalChartPairPresentation25_jacobian K pivot ⟨⟨j, k⟩, hj, hk, hjk⟩]
  exact Ideal.subset_span ⟨⟨⟨j, k⟩, hj, hk, hjk⟩, rfl⟩

end N25
