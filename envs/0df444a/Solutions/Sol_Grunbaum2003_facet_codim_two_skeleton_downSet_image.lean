-- Prove2me | solution 1 for Grunbaum2003.facet_codim_two_skeleton_downSet_image
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T19:09:00.265714+00:00
-- url     : https://prove2.me/submissions/268719c3-68d3-4569-ab6e-7fb4f2a2b51e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_vertex_figure_face_finrank_and_prescribed_cut
import Theorems.Thm_Grunbaum2003_facet_codim_two_skeleton_downSet_of_vertex_figure_cut
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem facet_codim_two_skeleton_downSet_image_sol (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by
  have hHullP := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hHullQ := polytope_face_eq_convexHull_exposed_vertices d Q hQ
  have hCutP := vertex_figure_face_finrank_and_prescribed_cut d P hP
  have hCutQ := vertex_figure_face_finrank_and_prescribed_cut d Q hQ
  have hVertNonempty : (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).Nonempty := by
    have hne : (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})).Nonempty := by
      rw [← hHullP.2 F]
      exact hFacet.1
    exact convexHull_nonempty_iff.mp hne
  obtain ⟨v, hvF, hvExp⟩ := hVertNonempty
  exact facet_codim_two_skeleton_downSet_of_vertex_figure_cut d hd P Q hP hQ
    hHullP hHullQ hCutP hCutQ φ F hFacet v hvExp hvF

end Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P) (hQ : Grunbaum2003.IsDPolytope Q)
    (φ : Grunbaum2003.SkeletonFace P (d - 2) ≃o Grunbaum2003.SkeletonFace Q (d - 2))
    (F : Grunbaum2003.PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) :
    ∃ G : Grunbaum2003.PolytopeFace Q,
      ∀ T : Grunbaum2003.SkeletonFace Q (d - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F :=
  Grunbaum2003.facet_codim_two_skeleton_downSet_image_sol d hd P Q hP hQ φ F hFacet
