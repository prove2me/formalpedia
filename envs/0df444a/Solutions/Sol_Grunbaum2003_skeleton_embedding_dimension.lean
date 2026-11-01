-- Prove2me | solution 1 for Grunbaum2003.skeleton_embedding_dimension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:26:57.522392+00:00
-- url     : https://prove2.me/submissions/4ffbbb3f-c321-4aaf-be23-add1c6a0477d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_skeletonCarrier
import Definitions.Def_Grunbaum2003_IsPolytopalComplex
import Definitions.Def_Grunbaum2003_skeletonEmbeddingDimension
import Theorems.Thm_Grunbaum2003_skeleton_cells_finite_polytope_inter_exposed
import Theorems.Thm_Grunbaum2003_skeletonEmbeddingDimension_realizable_and_lower_bounds
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Bounds.Defs

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), Theorem 11.1.9 (p. 204): for `1 ≤ k ≤ d` and any `d`-polytope `P`,
`skeletonEmbeddingDimension d k` is the least dimension for both topological embedding
of `skeletonCarrier P k` and polytopal-complex realization of `SkeletonFace P k`. -/
theorem skeleton_embedding_dimension_sol (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    IsLeast {m : ℕ | ∃ S : Set (Fin m → ℝ),
      Nonempty ((skeletonCarrier P k) ≃ₜ S)}
      (skeletonEmbeddingDimension d k) ∧
    IsLeast {m : ℕ | ∃ C : Set (Set (Fin m → ℝ)),
      IsPolytopalComplex C ∧ Nonempty (SkeletonFace P k ≃o C)}
      (skeletonEmbeddingDimension d k) :=
  skeletonEmbeddingDimension_realizable_and_lower_bounds d k hk hkd P hP
    (skeleton_cells_finite_polytope_inter_exposed d k P hP)

end Grunbaum2003

theorem solution (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d)
    (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P) :
    IsLeast {m : ℕ | ∃ S : Set (Fin m → ℝ),
      Nonempty ((Grunbaum2003.skeletonCarrier P k) ≃ₜ S)}
      (Grunbaum2003.skeletonEmbeddingDimension d k) ∧
    IsLeast {m : ℕ | ∃ C : Set (Set (Fin m → ℝ)),
      Grunbaum2003.IsPolytopalComplex C ∧ Nonempty (Grunbaum2003.SkeletonFace P k ≃o C)}
      (Grunbaum2003.skeletonEmbeddingDimension d k) :=
  Grunbaum2003.skeleton_embedding_dimension_sol d k hk hkd P hP
