-- Prove2me | solution 1 for Grunbaum2003.facet_exposed_vertex_image_of_vertex_figure_cut
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:16:11.609088+00:00
-- url     : https://prove2.me/submissions/46d3db0d-456d-457f-9be5-01175d013c61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Theorems.Thm_Grunbaum2003_skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
import Theorems.Thm_Grunbaum2003_facet_exposed_vertex_image_from_vertex_figure_skeleton_iso
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem facet_exposed_vertex_image_of_vertex_figure_cut_sol (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hHullP : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P, E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : {x : Fin d → ℝ | IsExposed ℝ Q {x}}.Finite ∧
      ∀ E : PolytopeFace Q, E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ Q {x}}))
    (hCutP :
      (∀ v : Fin d → ℝ, IsExposed ℝ P {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ P G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (hCutQ :
      (∀ v : Fin d → ℝ, IsExposed ℝ Q {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ Q, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ Q {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ Q {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ Q G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (vertexSkeletonFace : ∀ {e : ℕ} (R : Set (Fin e → ℝ)) (k : ℕ)
      (x : Fin e → ℝ), IsExposed ℝ R {x} → SkeletonFace R k)
    (hVertexVal : ∀ {e : ℕ} (R : Set (Fin e → ℝ)) (k : ℕ) (x : Fin e → ℝ) (hx : IsExposed ℝ R {x}),
      (vertexSkeletonFace R k x hx).val.val = {x})
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (hEmpty : ∀ S : SkeletonFace P (d - 2), (φ S).val.val = ∅ ↔ S.val.val = ∅)
    (hMapVert : ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      ∃ (y : Fin d → ℝ) (hy : IsExposed ℝ Q {y}),
        φ (vertexSkeletonFace P (d - 2) x hx) = vertexSkeletonFace Q (d - 2) y hy)
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v}) (hvF : v ∈ F.val) :
    ∃ G : PolytopeFace Q,
      ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        (φ (vertexSkeletonFace P (d - 2) x hx)).val ≤ G ↔ x ∈ F.val := by
  obtain ⟨hEdgeIso, hVertFigSkel⟩ :=
    skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
  exact facet_exposed_vertex_image_from_vertex_figure_skeleton_iso d hd
    P Q hP hQ hHullP hHullQ hCutP hCutQ
    (fun hR hS ψ T => hEdgeIso hR hS ψ T)
    hVertFigSkel vertexSkeletonFace hVertexVal φ hEmpty hMapVert F hFacet v hv hvF

end Grunbaum2003

open Grunbaum2003 in
theorem solution (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hHullP : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P, E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : {x : Fin d → ℝ | IsExposed ℝ Q {x}}.Finite ∧
      ∀ E : PolytopeFace Q, E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ Q {x}}))
    (hCutP :
      (∀ v : Fin d → ℝ, IsExposed ℝ P {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ P G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (hCutQ :
      (∀ v : Fin d → ℝ, IsExposed ℝ Q {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ Q, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ Q {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ Q {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ Q G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (vertexSkeletonFace : ∀ {e : ℕ} (R : Set (Fin e → ℝ)) (k : ℕ)
      (x : Fin e → ℝ), IsExposed ℝ R {x} → SkeletonFace R k)
    (hVertexVal : ∀ {e : ℕ} (R : Set (Fin e → ℝ)) (k : ℕ) (x : Fin e → ℝ) (hx : IsExposed ℝ R {x}),
      (vertexSkeletonFace R k x hx).val.val = {x})
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (hEmpty : ∀ S : SkeletonFace P (d - 2), (φ S).val.val = ∅ ↔ S.val.val = ∅)
    (hMapVert : ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      ∃ (y : Fin d → ℝ) (hy : IsExposed ℝ Q {y}),
        φ (vertexSkeletonFace P (d - 2) x hx) = vertexSkeletonFace Q (d - 2) y hy)
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v}) (hvF : v ∈ F.val) :
    ∃ G : PolytopeFace Q,
      ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        (φ (vertexSkeletonFace P (d - 2) x hx)).val ≤ G ↔ x ∈ F.val :=
  Grunbaum2003.facet_exposed_vertex_image_of_vertex_figure_cut_sol d hd
    P Q hP hQ hHullP hHullQ hCutP hCutQ vertexSkeletonFace hVertexVal
    φ hEmpty hMapVert F hFacet v hv hvF
