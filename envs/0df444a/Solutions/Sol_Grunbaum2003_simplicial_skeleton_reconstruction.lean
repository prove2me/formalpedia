-- Prove2me | solution 1 for Grunbaum2003.simplicial_skeleton_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:26:56.525671+00:00
-- url     : https://prove2.me/submissions/9ecd2110-e128-4dcd-889d-b47fef4c16da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_downSet_image
import Theorems.Thm_Grunbaum2003_simplicial_half_skeleton_dim_and_downSet_image

set_option autoImplicit false

namespace Grunbaum2003

/-- Perles's simplicial reconstruction theorem (Grünbaum 2003, §12.4, p. 234a): the
`⌊d / 2⌋`-skeleton of a simplicial `d`-polytope `P` determines both the dimension `e = d`
and the complete face lattice of any `e`-polytope `Q` with order-isomorphic `⌊d / 2⌋`-skeleton. -/
theorem simplicial_skeleton_reconstruction_sol (d e : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : IsSimplicialDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d / 2) ≃o SkeletonFace Q (d / 2)) :
    e = d ∧ ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P (d / 2), Φ F.val = (φ F).val := by
  obtain ⟨hed, hFwd, hBwd⟩ :=
    simplicial_half_skeleton_dim_and_downSet_image d e P Q hP hQ φ
  exact ⟨hed,
    skeleton_orderIso_extends_of_downSet_image d e (d / 2) P Q hP.1 hQ φ hFwd hBwd⟩

end Grunbaum2003

theorem solution (d e : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : Grunbaum2003.IsSimplicialDPolytope P) (hQ : Grunbaum2003.IsDPolytope Q)
    (φ : Grunbaum2003.SkeletonFace P (d / 2) ≃o Grunbaum2003.SkeletonFace Q (d / 2)) :
    e = d ∧ ∃ Φ : Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q,
      ∀ F : Grunbaum2003.SkeletonFace P (d / 2), Φ F.val = (φ F).val :=
  Grunbaum2003.simplicial_skeleton_reconstruction_sol d e P Q hP hQ φ
