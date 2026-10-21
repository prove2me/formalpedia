-- Prove2me | solution 1 for GeometryOfGraphs.Clique.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:38:30.341366+00:00
-- url     : https://prove2.me/submissions/e697bb14-3f36-4700-adc3-304d001bfd15

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_isoDim

set_option autoImplicit false
open GeometryOfGraphs.Clique

theorem solution (X : Type*) [Fintype X] [PseudoMetricSpace X] :
    ∃ φ : X → (Fin (Fintype.card X) → ℝ),
      ∀ x y, (∀ k, |φ x k - φ y k| ≤ dist x y) ∧
        ∃ k, |φ x k - φ y k| = dist x y := by
  classical
  let e := (Fintype.equivFin X).symm
  refine ⟨fun x k => dist x (e k), fun x y => ⟨fun k => abs_dist_sub_le x y (e k), ?_⟩⟩
  refine ⟨Fintype.equivFin X x, ?_⟩
  simp [e, dist_comm]
