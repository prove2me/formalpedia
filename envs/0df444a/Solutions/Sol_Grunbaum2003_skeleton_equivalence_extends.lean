-- Prove2me | solution 1 for Grunbaum2003.skeleton_equivalence_extends
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:26:54.321672+00:00
-- url     : https://prove2.me/submissions/f3fe577b-e060-429b-83d1-a2de932d051d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Theorems.Thm_Grunbaum2003_polytopeFace_trichotomy_codim_two
import Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_downSet_image
import Theorems.Thm_Grunbaum2003_facet_codim_two_skeleton_downSet_image
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), Theorem 12.3.1 (pp. 228, 231): every order isomorphism between the
`(d - 2)`-skeletons of two `d`-polytopes in dimension `d ≥ 3` extends to an order
isomorphism of their full face lattices. -/
theorem skeleton_equivalence_extends_sol (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2)) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val := by
  have hd_pos : 0 < d := by omega
  refine skeleton_orderIso_extends_of_downSet_image d d (d - 2) P Q hP hQ φ ?_ ?_
  · intro F
    rcases polytopeFace_trichotomy_codim_two d hd_pos P F with hSkel | hTop | hFacet
    · refine ⟨(φ ⟨F, hSkel⟩).val, ?_⟩
      intro T
      change T ≤ φ ⟨F, hSkel⟩ ↔ φ.symm T ≤ ⟨F, hSkel⟩
      rw [← φ.map_rel_iff, φ.apply_symm_apply]
    · have hQ_exp : IsExposed ℝ Q Q := fun _ => ⟨0, by simp⟩
      refine ⟨⟨Q, hQ_exp⟩, ?_⟩
      intro T
      have h1 : T.val ≤ (⟨Q, hQ_exp⟩ : PolytopeFace Q) := T.val.2.subset
      have h2 : (φ.symm T).val ≤ F := by
        change (φ.symm T).val.val ⊆ F.val
        rw [hTop]
        exact (φ.symm T).val.2.subset
      exact iff_of_true h1 h2
    · exact facet_codim_two_skeleton_downSet_image d hd P Q hP hQ φ F hFacet
  · intro G
    rcases polytopeFace_trichotomy_codim_two d hd_pos Q G with hSkel | hTop | hFacet
    · refine ⟨(φ.symm ⟨G, hSkel⟩).val, ?_⟩
      intro S
      change S ≤ φ.symm ⟨G, hSkel⟩ ↔ φ S ≤ ⟨G, hSkel⟩
      rw [← φ.map_rel_iff, φ.apply_symm_apply]
    · have hP_exp : IsExposed ℝ P P := fun _ => ⟨0, by simp⟩
      refine ⟨⟨P, hP_exp⟩, ?_⟩
      intro S
      have h1 : S.val ≤ (⟨P, hP_exp⟩ : PolytopeFace P) := S.val.2.subset
      have h2 : (φ S).val ≤ G := by
        change (φ S).val.val ⊆ G.val
        rw [hTop]
        exact (φ S).val.2.subset
      exact iff_of_true h1 h2
    · obtain ⟨F, hF⟩ :=
        facet_codim_two_skeleton_downSet_image d hd Q P hQ hP φ.symm G hFacet
      refine ⟨F, fun S => ?_⟩
      simpa using hF S

end Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ))
    (hP : Grunbaum2003.IsDPolytope P) (hQ : Grunbaum2003.IsDPolytope Q)
    (φ : Grunbaum2003.SkeletonFace P (d - 2) ≃o Grunbaum2003.SkeletonFace Q (d - 2)) :
    ∃ Φ : Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q,
      ∀ F : Grunbaum2003.SkeletonFace P (d - 2), Φ F.val = (φ F).val :=
  Grunbaum2003.skeleton_equivalence_extends_sol d hd P Q hP hQ φ
