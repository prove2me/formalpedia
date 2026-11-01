-- Prove2me | solution 1 for Grunbaum2003.blind_mani_graph_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:26:55.409281+00:00
-- url     : https://prove2.me/submissions/ef08f27a-aa60-43cb-a27f-67a9df40bd20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_PolytopeVertex
import Definitions.Def_Grunbaum2003_polytopeGraph
import Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_le_succ
import Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_downSet_image
import Theorems.Thm_Grunbaum2003_blind_mani_simple_one_skeleton_downSet_image
import Mathlib.Tactic

set_option autoImplicit false

namespace Grunbaum2003

/-- Blind–Mani theorem (Grünbaum 2003, §12.4, p. 234a): every order isomorphism of the
`1`-skeleton of a simple `d`-polytope `P` onto the `1`-skeleton of a `d`-polytope `Q`
extends to an order isomorphism of their full face lattices. -/
theorem blind_mani_graph_reconstruction_sol (d : ℕ)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hSimple : ∀ v : PolytopeVertex P,
      ((polytopeGraph P).neighborSet v).ncard = d)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P 1, Φ F.val = (φ F).val := by
  by_cases hd2 : d ≤ 2
  · exact skeleton_orderIso_extends_of_le_succ d 1 hd2 P Q hP hQ φ
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨hFwd, hBwd⟩ :=
      blind_mani_simple_one_skeleton_downSet_image d hd3 P Q hP hQ hSimple φ
    exact skeleton_orderIso_extends_of_downSet_image d d 1 P Q hP hQ φ hFwd hBwd

end Grunbaum2003

theorem solution (d : ℕ)
    (P Q : Set (Fin d → ℝ))
    (hP : Grunbaum2003.IsDPolytope P) (hQ : Grunbaum2003.IsDPolytope Q)
    (hSimple : ∀ v : Grunbaum2003.PolytopeVertex P,
      ((Grunbaum2003.polytopeGraph P).neighborSet v).ncard = d)
    (φ : Grunbaum2003.SkeletonFace P 1 ≃o Grunbaum2003.SkeletonFace Q 1) :
    ∃ Φ : Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q,
      ∀ F : Grunbaum2003.SkeletonFace P 1, Φ F.val = (φ F).val :=
  Grunbaum2003.blind_mani_graph_reconstruction_sol d P Q hP hQ hSimple φ
