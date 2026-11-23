-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:04.859474+00:00
-- url     : https://prove2.me/submissions/bd1af555-1e7a-4e83-873a-f5ee7b635ba0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MixedCloning_Optimal_exists_projector_le_averageOverlap
import Theorems.Thm_MixedCloning_Optimal_averageOverlap_le_transposedIntegrals

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (d r n m : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (C : MixedCloning.Optimal.Cloner d n m) (hC : QAlgorithms.IsChannel C)
    (hperm : MixedCloning.Optimal.PermInvariant d n m C)
    (b : (L : YoungDiagram) → MixedCloning.Optimal.SchurBasis L d) :
    ∃ P : MixedCloning.Optimal.Op (Fin d), MixedCloning.Optimal.IsProjector r P ∧
      MixedCloning.Optimal.overlap d r n m C P ≤
        ∑ L ∈ MixedCloning.Optimal.partitions n r, (MixedCloning.Optimal.spechtDim L : ℝ) *
          MixedCloning.Optimal.schurCount L d / (r : ℝ)^n *
          sSup ((MixedCloning.Optimal.partitions m r).image fun M =>
            MixedCloning.Optimal.operatorNorm
              (MixedCloning.Optimal.transposedIntegral r L M (b L) (b M))) := by
  obtain ⟨P, hP, havg⟩ :=
    MixedCloning.Optimal.exists_projector_le_averageOverlap d r n m hrd C hC
  refine ⟨P, hP, havg.trans ?_⟩
  exact MixedCloning.Optimal.averageOverlap_le_transposedIntegrals d r n m hr hrd C hC hperm b
