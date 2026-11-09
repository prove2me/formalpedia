-- Prove2me | solution 2 for Grunbaum2003.skeleton_equivalence_extends
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T20:59:17.235902+00:00
-- url     : https://prove2.me/submissions/c9c6b55b-0643-40dc-9a59-ccd964c14cfc

import Theorems.Thm_Grunbaum2003_three_polytope_graph_equivalence_extends
import Theorems.Thm_Grunbaum2003_facet_downSet_image_of_lower_dim_reconstruction
import Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_downSet_image
import Theorems.Thm_Grunbaum2003_polytopeFace_trichotomy_codim_two
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

open Grunbaum2003

/-- Forward face images for every face, assuming the facet case. -/
theorem Grunbaum2003Skel.fwd_all (d : ℕ) (hd : 3 ≤ d)
    (ih : ∀ (P Q : Set (Fin d → ℝ)), IsDPolytope P → IsDPolytope Q →
      ∀ φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2),
        ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
          ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d + 1 - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by
  rcases polytopeFace_trichotomy_codim_two (d + 1) (by omega) P F with hS | hTop | hFacet
  · let S : SkeletonFace P (d + 1 - 2) := ⟨F, hS⟩
    refine ⟨(φ S).val, fun T => ?_⟩
    change T ≤ φ S ↔ φ.symm T ≤ S
    exact (OrderIso.symm_apply_le φ).symm
  · refine ⟨⟨Q, IsExposed.refl Q⟩, fun T => ?_⟩
    constructor
    · intro _
      change (φ.symm T).val.val ⊆ F.val
      rw [hTop]
      exact (φ.symm T).val.property.subset
    · intro _
      change T.val.val ⊆ Q
      exact T.val.property.subset
  · have hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d := by
      refine ⟨hFacet.1, ?_⟩
      rw [hFacet.2]
      omega
    exact facet_downSet_image_of_lower_dim_reconstruction d hd ih P Q hP hQ φ F hF

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2)) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val := by
  induction d, hd using Nat.le_induction with
  | base => exact three_polytope_graph_equivalence_extends P Q hP hQ φ
  | succ d hd ih =>
    refine skeleton_orderIso_extends_of_downSet_image (d + 1) (d + 1) (d + 1 - 2) P Q hP hQ φ
      (fun F => Grunbaum2003Skel.fwd_all d hd ih P Q hP hQ φ F) (fun G => ?_)
    obtain ⟨F, hF⟩ := Grunbaum2003Skel.fwd_all d hd ih Q P hQ hP φ.symm G
    exact ⟨F, fun S => hF S⟩
