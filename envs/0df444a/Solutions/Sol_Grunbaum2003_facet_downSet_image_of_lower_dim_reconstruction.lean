-- Prove2me | solution 1 for Grunbaum2003.facet_downSet_image_of_lower_dim_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:13:55.922201+00:00
-- url     : https://prove2.me/submissions/b185a0d8-9e14-4422-8c59-382611551669

import Theorems.Thm_Grunbaum2003_exists_compatible_local_facet_and_two_ridge_gluing
import Theorems.Thm_Grunbaum2003_global_facet_from_compatible_local_facets_and_ridge_gluing
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

open Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (ih : ∀ (P Q : Set (Fin d → ℝ)), IsDPolytope P → IsDPolytope Q →
      ∀ φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2),
        ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
          ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d + 1 - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by
  obtain ⟨hLocal, hGlue⟩ :=
    exists_compatible_local_facet_and_two_ridge_gluing d hd ih P Q hP hQ φ F hF
  exact global_facet_from_compatible_local_facets_and_ridge_gluing d hd P Q hP hQ φ F hF hLocal hGlue
