-- Prove2me | solution 1 for Grunbaum2003.facet_exposed_vertex_image_from_vertex_figure_skeleton_iso
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:35:26.830913+00:00
-- url     : https://prove2.me/submissions/685d240e-79fc-417d-91e3-6ba9defd15a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Theorems.Thm_Grunbaum2003_vertex_figure_induced_skeleton_iso_and_upper_interval_lift
import Theorems.Thm_Grunbaum2003_facet_exposed_vertex_image_from_vertex_figure_lift
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem facet_exposed_vertex_image_from_vertex_figure_skeleton_iso_sol (d : ℕ) (hd : 3 ≤ d)
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
    (hEdgeIso : ∀ {e f k l : ℕ} {R : Set (Fin e → ℝ)} {S : Set (Fin f → ℝ)},
      ({x : Fin e → ℝ | IsExposed ℝ R {x}}.Finite ∧
        ∀ E : PolytopeFace R,
          E.val = convexHull ℝ (E.val ∩ {x : Fin e → ℝ | IsExposed ℝ R {x}})) →
      ({y : Fin f → ℝ | IsExposed ℝ S {y}}.Finite ∧
        ∀ E : PolytopeFace S,
          E.val = convexHull ℝ (E.val ∩ {y : Fin f → ℝ | IsExposed ℝ S {y}})) →
      ∀ (ψ : SkeletonFace R k ≃o SkeletonFace S l) (T : SkeletonFace R k),
        ((ψ T).val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ (ψ T).val.val).direction = 1) ↔
        (T.val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ T.val.val).direction = 1))
    (hVertFigSkel : ∀ (e : ℕ), 0 < e → ∀ (R : Set (Fin e → ℝ)), IsDPolytope R →
      ({x : Fin e → ℝ | IsExposed ℝ R {x}}.Finite ∧
        ∀ E : PolytopeFace R,
          E.val = convexHull ℝ (E.val ∩ {x : Fin e → ℝ | IsExposed ℝ R {x}})) →
      ((∀ v : Fin e → ℝ, IsExposed ℝ R {v} →
          ∃ (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ),
            α < l v ∧ (∀ x ∈ R, l x ≤ l v) ∧
            ∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v →
              l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
        (∀ (v : Fin e → ℝ) (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ),
          α < l v →
          (∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v → l w < α) →
          ∀ (G : Set (Fin e → ℝ)), IsExposed ℝ R G → v ∈ G →
            affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
            ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
            (G ≠ {v} →
              (G ∩ l ⁻¹' {α}).Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ G).direction =
                  Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1))) →
      ∀ (v : Fin e → ℝ), IsExposed ℝ R {v} →
        ∃ (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ)
          (Q₀ : Set (Fin (e - 1) → ℝ))
          (f : (Fin (e - 1) → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
          (Ψ : {G : PolytopeFace R // v ∈ G.val} ≃o PolytopeFace Q₀),
          α < l v ∧
          (∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v → l w < α) ∧
          IsDPolytope Q₀ ∧
          Function.Injective f ∧
          f '' Q₀ = R ∩ l ⁻¹' {α} ∧
          (∀ G : {G : PolytopeFace R // v ∈ G.val},
            f '' (Ψ G).val = G.val.val ∩ (R ∩ l ⁻¹' {α}) ∧
            ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
            (G.val.val ≠ {v} →
              (Ψ G).val.Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
                  Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1)) ∧
          (∀ k : ℕ,
            ∃ Ψ_skel : {S : SkeletonFace R (k + 1) // v ∈ S.val.val} ≃o
                SkeletonFace Q₀ k,
              ∀ S : {S : SkeletonFace R (k + 1) // v ∈ S.val.val},
                (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩))
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
  obtain ⟨hFacetShift, hCodimTwoSkel, hInducedLift⟩ :=
    vertex_figure_induced_skeleton_iso_and_upper_interval_lift
  obtain ⟨v', hv', hφv⟩ := hMapVert v hv
  obtain ⟨_, _, P_v, _, Ψ_P, _, _, hP_v, _, _, hΨ_P_props, hΨ_P_skel⟩ :=
    hVertFigSkel d (by omega) P hP hHullP hCutP v hv
  obtain ⟨_, _, Q_v', _, Ψ_Q, _, _, hQ_v', _, _, hΨ_Q_props, hΨ_Q_skel⟩ :=
    hVertFigSkel d (by omega) Q hQ hHullQ hCutQ v' hv'
  obtain ⟨Ψ_skel_P, hΨ_skel_P⟩ := hCodimTwoSkel hd Ψ_P hΨ_P_skel
  obtain ⟨Ψ_skel_Q, hΨ_skel_Q⟩ := hCodimTwoSkel hd Ψ_Q hΨ_Q_skel
  have hFacet_v :
      (Ψ_P ⟨F, hvF⟩).val.Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ (Ψ_P ⟨F, hvF⟩).val).direction = d - 2 :=
    hFacetShift (by omega) Ψ_P (fun G => (hΨ_P_props G).2.2) F hFacet hvF
  obtain ⟨φ_v, hLift⟩ :=
    hInducedLift vertexSkeletonFace hVertexVal φ v hv v' hv' hφv
      Ψ_P Ψ_Q Ψ_skel_P hΨ_skel_P Ψ_skel_Q hΨ_skel_Q
  exact facet_exposed_vertex_image_from_vertex_figure_lift d hd
    P Q hP hQ hHullP hHullQ hCutP hCutQ
    (fun hR hS ψ T => hEdgeIso hR hS ψ T)
    hVertFigSkel vertexSkeletonFace hVertexVal φ hEmpty hMapVert
    F hFacet v hv hvF v' hv' hφv P_v Q_v' hP_v hQ_v' Ψ_P Ψ_Q hFacet_v φ_v
    (hLift F hvF)

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
    (hEdgeIso : ∀ {e f k l : ℕ} {R : Set (Fin e → ℝ)} {S : Set (Fin f → ℝ)},
      ({x : Fin e → ℝ | IsExposed ℝ R {x}}.Finite ∧
        ∀ E : PolytopeFace R,
          E.val = convexHull ℝ (E.val ∩ {x : Fin e → ℝ | IsExposed ℝ R {x}})) →
      ({y : Fin f → ℝ | IsExposed ℝ S {y}}.Finite ∧
        ∀ E : PolytopeFace S,
          E.val = convexHull ℝ (E.val ∩ {y : Fin f → ℝ | IsExposed ℝ S {y}})) →
      ∀ (ψ : SkeletonFace R k ≃o SkeletonFace S l) (T : SkeletonFace R k),
        ((ψ T).val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ (ψ T).val.val).direction = 1) ↔
        (T.val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ T.val.val).direction = 1))
    (hVertFigSkel : ∀ (e : ℕ), 0 < e → ∀ (R : Set (Fin e → ℝ)), IsDPolytope R →
      ({x : Fin e → ℝ | IsExposed ℝ R {x}}.Finite ∧
        ∀ E : PolytopeFace R,
          E.val = convexHull ℝ (E.val ∩ {x : Fin e → ℝ | IsExposed ℝ R {x}})) →
      ((∀ v : Fin e → ℝ, IsExposed ℝ R {v} →
          ∃ (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ),
            α < l v ∧ (∀ x ∈ R, l x ≤ l v) ∧
            ∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v →
              l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
        (∀ (v : Fin e → ℝ) (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ),
          α < l v →
          (∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v → l w < α) →
          ∀ (G : Set (Fin e → ℝ)), IsExposed ℝ R G → v ∈ G →
            affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
            ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
            (G ≠ {v} →
              (G ∩ l ⁻¹' {α}).Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ G).direction =
                  Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1))) →
      ∀ (v : Fin e → ℝ), IsExposed ℝ R {v} →
        ∃ (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ)
          (Q₀ : Set (Fin (e - 1) → ℝ))
          (f : (Fin (e - 1) → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
          (Ψ : {G : PolytopeFace R // v ∈ G.val} ≃o PolytopeFace Q₀),
          α < l v ∧
          (∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v → l w < α) ∧
          IsDPolytope Q₀ ∧
          Function.Injective f ∧
          f '' Q₀ = R ∩ l ⁻¹' {α} ∧
          (∀ G : {G : PolytopeFace R // v ∈ G.val},
            f '' (Ψ G).val = G.val.val ∩ (R ∩ l ⁻¹' {α}) ∧
            ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
            (G.val.val ≠ {v} →
              (Ψ G).val.Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
                  Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1)) ∧
          (∀ k : ℕ,
            ∃ Ψ_skel : {S : SkeletonFace R (k + 1) // v ∈ S.val.val} ≃o
                SkeletonFace Q₀ k,
              ∀ S : {S : SkeletonFace R (k + 1) // v ∈ S.val.val},
                (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩))
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
  Grunbaum2003.facet_exposed_vertex_image_from_vertex_figure_skeleton_iso_sol d hd
    P Q hP hQ hHullP hHullQ hCutP hCutQ hEdgeIso hVertFigSkel
    vertexSkeletonFace hVertexVal φ hEmpty hMapVert F hFacet v hv hvF
