-- Prove2me | solution 1 for N25.canonicalChartPairPresentation25_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:01.951554+00:00
-- url     : https://prove2.me/submissions/edb149d6-e883-42dc-bac1-05e7485e74d8

import Mathlib
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Smooth canonical charts, with relative dimension one from their literal presentations. -/
noncomputable section

namespace N25

/-- Expansion in the pivot relation identifies the selected presentation
Jacobian with the literal non-pivot minor. -/
theorem _root_.solution (K : Type*) [CommRing K]
    (pivot : Fin 4) (pair : CanonicalChartColumnPair25 pivot) :
    (canonicalChartPairPresentation25 K pivot pair).jacobian =
      Ideal.Quotient.mk (canonicalChartIdeal25 K pivot)
        (canonicalJacobianMinor25 K pair.val.1 pair.val.2) := by
  have hdet :
      (Algebra.PreSubmersivePresentation.naive (v := canonicalChartRelations25 K pivot)
        (canonicalChartPairColumns25 pivot pair) (canonicalChartPairColumns25_injective pivot pair)).jacobiMatrix.det =
          canonicalJacobianMinor25 K pair.val.1 pair.val.2 := by
    have hmatrix :
        (Algebra.PreSubmersivePresentation.naive (v := canonicalChartRelations25 K pivot)
          (canonicalChartPairColumns25 pivot pair)
          (canonicalChartPairColumns25_injective pivot pair)).jacobiMatrix =
        Matrix.of (fun a b : Fin 3 =>
          MvPolynomial.pderiv (canonicalChartPairColumns25 pivot pair a)
            (canonicalChartRelations25 K pivot b)) := by
      apply Matrix.ext
      intro a b
      simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, Matrix.of_apply]
    rw [hmatrix]
    rcases pair with ⟨⟨j, k⟩, hj, hk, hjk⟩
    dsimp only at hj hk hjk
    simp [Matrix.det_fin_three, canonicalChartPairColumns25, canonicalChartRelations25,
      canonicalJacobianMinor25, hj, hk, Ne.symm hj, Ne.symm hk] <;> ring
  rw [canonicalChartPairPresentation25, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change Ideal.Quotient.mk (canonicalChartIdeal25 K pivot) _ = _
  exact congrArg (Ideal.Quotient.mk (canonicalChartIdeal25 K pivot)) hdet

end N25
