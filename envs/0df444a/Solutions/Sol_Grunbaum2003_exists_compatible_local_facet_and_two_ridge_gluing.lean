-- Prove2me | solution 1 for Grunbaum2003.exists_compatible_local_facet_and_two_ridge_gluing
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:13:55.302612+00:00
-- url     : https://prove2.me/submissions/ee5d1e35-c2af-443d-ad94-d90b497e8560

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_vertex_figure_face_finrank_and_prescribed_cut
import Theorems.Thm_Grunbaum2003_skeleton_iso_preserves_exposed_vertices_and_reduces_downSet
import Theorems.Thm_Grunbaum2003_skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
import Theorems.Thm_Grunbaum2003_vertex_figure_induced_skeleton_iso_and_upper_interval_lift
import Theorems.Thm_Grunbaum2003_polytopeFace_trichotomy_codim_two

set_option autoImplicit false

namespace Grunbaum2003Compat
open Grunbaum2003

/-- A nonempty face contained in another face of at most the same dimension equals it. -/
theorem face_eq_of_le_of_finrank_le {n : ℕ} {P : Set (Fin n → ℝ)} (G F : PolytopeFace P)
    (hG : G.val.Nonempty) (hle : G ≤ F)
    (hdim : Module.finrank ℝ (affineSpan ℝ F.val).direction ≤
      Module.finrank ℝ (affineSpan ℝ G.val).direction) : G = F := by
  obtain ⟨g, hg⟩ := hG
  obtain ⟨l, hl⟩ := G.property ⟨g, hg⟩
  rw [direction_affineSpan, direction_affineSpan] at hdim
  have hgG := hg
  rw [hl] at hgG
  have hconst : ∀ x ∈ G.val, l x = l g := by
    intro x hx
    rw [hl] at hx
    exact le_antisymm (hgG.2 x hx.1) (hx.2 g hgG.1)
  have hker : vectorSpan ℝ G.val ≤ LinearMap.ker (l : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp [hconst a ha, hconst b hb]
  have hspan : vectorSpan ℝ G.val = vectorSpan ℝ F.val :=
    Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hle) hdim
  have hFconst : ∀ y ∈ F.val, l y = l g := by
    intro y hy
    have hmem : y -ᵥ g ∈ vectorSpan ℝ F.val := vsub_mem_vectorSpan ℝ hy (hle hg)
    rw [← hspan] at hmem
    have := hker hmem
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] at this
    linarith
  apply le_antisymm hle
  intro y hy
  have hyP : y ∈ P := F.property.subset hy
  rw [hl]
  refine ⟨hyP, fun z hz => ?_⟩
  rw [hFconst y hy]
  exact hgG.2 z hz

/-- Every order isomorphism `Φ : PolytopeFace P ≃o PolytopeFace Q` between `d`-polytopes (`d ≥ 3`)
extending a `(d - 2)`-skeleton isomorphism `φ` maps facets (`finrank = d - 1`) to facets. -/
theorem orderIso_extending_skeleton_preserves_facets {d : ℕ} (hd : 3 ≤ d)
    {P Q : Set (Fin d → ℝ)} (hP : IsDPolytope P) (_hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (Φ : PolytopeFace P ≃o PolytopeFace Q)
    (hΦ : ∀ S : SkeletonFace P (d - 2), Φ S.val = (φ S).val)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) :
    (Φ F).val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (Φ F).val).direction = d - 1 := by
  have hFP : F ≠ ⟨P, IsExposed.refl P⟩ := by
    intro hEq
    have h1 : F.val = P := congrArg Subtype.val hEq
    have h2 : Module.finrank ℝ (affineSpan ℝ P).direction = d := by
      rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
    rw [h1, h2] at hF
    omega
  have hTop : Φ ⟨P, IsExposed.refl P⟩ = ⟨Q, IsExposed.refl Q⟩ := by
    apply le_antisymm
    · exact (Φ ⟨P, IsExposed.refl P⟩).property.subset
    · have hle : Φ.symm ⟨Q, IsExposed.refl Q⟩ ≤ ⟨P, IsExposed.refl P⟩ :=
        (Φ.symm ⟨Q, IsExposed.refl Q⟩).property.subset
      exact (Φ.symm_apply_le).mp hle
  rcases polytopeFace_trichotomy_codim_two d (by omega) Q (Φ F) with hSkel | hFull | hFacet
  · let T : SkeletonFace Q (d - 2) := ⟨Φ F, hSkel⟩
    have hEq : Φ (φ.symm T).val = Φ F := by
      rw [hΦ (φ.symm T), OrderIso.apply_symm_apply]
    have hFEq : (φ.symm T).val = F := Φ.injective hEq
    rcases (φ.symm T).property with hEmpty | hSmall
    · rw [hFEq] at hEmpty
      rw [hEmpty] at hF
      exact False.elim (Set.not_nonempty_empty hF.1)
    · rw [hFEq, hF.2] at hSmall
      omega
  · have hEq : Φ F = Φ ⟨P, IsExposed.refl P⟩ := by
      rw [hTop]
      exact Subtype.ext hFull
    exact False.elim (hFP (Φ.injective hEq))
  · exact hFacet

/-- Using the dimension-`d` induction hypothesis on vertex figures, every vertex `v ∈ F` of a facet `F`
of a `(d + 1)`-polytope `P` admits a local facet `G_v` of `Q` containing the mapped vertex `v'` whose
upper interval in the `(d - 1)`-skeleton matches `F`'s upper interval at `v` under `φ`. -/
theorem exists_compatible_local_facet_at_vertex (d : ℕ) (hd : 3 ≤ d)
    (ih : ∀ (P Q : Set (Fin d → ℝ)), IsDPolytope P → IsDPolytope Q →
      ∀ φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2),
        ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
          ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d)
    (v : Fin (d + 1) → ℝ) (hv : IsExposed ℝ P {v}) (hvF : v ∈ F.val) :
    ∃ G : PolytopeFace Q,
      G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
      (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)) := by
  have hHullP := polytope_face_eq_convexHull_exposed_vertices (d + 1) P hP
  have hHullQ := polytope_face_eq_convexHull_exposed_vertices (d + 1) Q hQ
  have hCutP := vertex_figure_face_finrank_and_prescribed_cut (d + 1) P hP
  have hCutQ := vertex_figure_face_finrank_and_prescribed_cut (d + 1) Q hQ
  obtain ⟨vertexSkeletonFace, hVertexVal, hVertIso⟩ :=
    skeleton_iso_preserves_exposed_vertices_and_reduces_downSet
  obtain ⟨_, hMapVert, _⟩ := hVertIso hHullP.2 hHullQ.2 φ
  obtain ⟨v', hv', hφv⟩ := hMapVert v hv
  obtain ⟨_, hVertFig⟩ := skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
  obtain ⟨lP, αP, P_v, fP, Ψ_P, _, _, hP_v, _, _, hΨ_P_props, hΨ_P_skel⟩ :=
    hVertFig (d + 1) (by omega) P hP hHullP hCutP v hv
  obtain ⟨lQ, αQ, Q_v', fQ, Ψ_Q, _, _, hQ_v', _, _, hΨ_Q_props, hΨ_Q_skel⟩ :=
    hVertFig (d + 1) (by omega) Q hQ hHullQ hCutQ v' hv'
  obtain ⟨hDimDrop, hSkelDrop, hInducedLift⟩ :=
    vertex_figure_induced_skeleton_iso_and_upper_interval_lift
  obtain ⟨Ψ_skel_P, hΨ_skel_P⟩ := hSkelDrop (d := d + 1) (by omega) Ψ_P hΨ_P_skel
  obtain ⟨Ψ_skel_Q, hΨ_skel_Q⟩ := hSkelDrop (d := d + 1) (by omega) Ψ_Q hΨ_Q_skel
  obtain ⟨φ_v, hφ_v_lift⟩ := hInducedLift
    vertexSkeletonFace hVertexVal φ v hv v' hv' hφv Ψ_P Ψ_Q
    Ψ_skel_P hΨ_skel_P Ψ_skel_Q hΨ_skel_Q
  obtain ⟨Φ_v, hΦ_v⟩ := ih P_v Q_v' hP_v hQ_v' φ_v
  let F_v : PolytopeFace P_v := Ψ_P ⟨F, hvF⟩
  have hF_v : F_v.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F_v.val).direction = d - 1 :=
    hDimDrop (d := d + 1) (by omega) Ψ_P (fun G hG => (hΨ_P_props G).2.2 hG) F hF hvF
  let G_v' : PolytopeFace Q_v' := Φ_v F_v
  have hG_v' : G_v'.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_v'.val).direction = d - 1 :=
    orderIso_extending_skeleton_preserves_facets hd hP_v hQ_v' φ_v Φ_v hΦ_v F_v hF_v
  have hG_v'_down : ∀ T₀ : SkeletonFace Q_v' (d - 2),
      T₀.val ≤ G_v' ↔ (φ_v.symm T₀).val ≤ F_v := by
    intro T₀
    have h1 : (φ_v (φ_v.symm T₀)).val = T₀.val := by simp
    have h2 : Φ_v (φ_v.symm T₀).val = (φ_v (φ_v.symm T₀)).val := hΦ_v (φ_v.symm T₀)
    rw [← h1, ← h2]
    exact Φ_v.le_iff_le
  have hLift := hφ_v_lift F hvF G_v' hG_v'_down
  let G_sub : {H : PolytopeFace Q // v' ∈ H.val} := Ψ_Q.symm G_v'
  let G : PolytopeFace Q := G_sub.val
  have hΨ_G : Ψ_Q G_sub = G_v' := OrderIso.apply_symm_apply Ψ_Q G_v'
  have hG_ne_v' : G.val ≠ {v'} := by
    intro hEq
    have hEmpty : (Ψ_Q G_sub).val = ∅ := ((hΨ_Q_props G_sub).2.1).mpr hEq
    rw [hΨ_G] at hEmpty
    rw [hEmpty] at hG_v'
    exact Set.not_nonempty_empty hG_v'.1
  have hG_dim : Module.finrank ℝ (affineSpan ℝ G.val).direction = d := by
    have hStep : Module.finrank ℝ (affineSpan ℝ G.val).direction =
        Module.finrank ℝ (affineSpan ℝ (Ψ_Q G_sub).val).direction + 1 :=
      ((hΨ_Q_props G_sub).2.2 hG_ne_v').2
    rw [hΨ_G, hG_v'.2] at hStep
    omega
  exact ⟨G, ⟨v', G_sub.property⟩, hG_dim, hLift.2⟩

/-- Two facets of a polytope sharing two distinct ridges coincide. -/
theorem facets_eq_of_two_shared_ridges (n : ℕ) (P : Set (Fin n → ℝ))
    (F F' R₁ R₂ : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = n - 1)
    (hF' : F'.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F'.val).direction = n - 1)
    (hR₁ : R₁.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ R₁.val).direction = n - 2)
    (hR₂ : R₂.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ R₂.val).direction = n - 2)
    (hne : R₁ ≠ R₂) (h₁ : R₁ ≤ F) (h₁' : R₁ ≤ F') (h₂ : R₂ ≤ F) (h₂' : R₂ ≤ F') :
    F = F' := by
  by_contra hFF
  let I : PolytopeFace P := ⟨F.val ∩ F'.val, F.property.inter F'.property⟩
  have hIne : I.val.Nonempty := by
    obtain ⟨x, hx⟩ := hR₁.1
    exact ⟨x, h₁ hx, h₁' hx⟩
  have hIF : I ≤ F := fun x hx => hx.1
  have hIF' : I ≤ F' := fun x hx => hx.2
  have hIlt : Module.finrank ℝ (affineSpan ℝ I.val).direction < n - 1 := by
    by_contra hge
    have e1 : I = F := face_eq_of_le_of_finrank_le I F hIne hIF (by omega)
    have e2 : I = F' := face_eq_of_le_of_finrank_le I F' hIne hIF' (by omega)
    exact hFF (e1.symm.trans e2)
  have hR₁I : R₁ ≤ I := fun x hx => ⟨h₁ hx, h₁' hx⟩
  have hR₂I : R₂ ≤ I := fun x hx => ⟨h₂ hx, h₂' hx⟩
  have e₁ : R₁ = I := face_eq_of_le_of_finrank_le R₁ I hR₁.1 hR₁I (by omega)
  have e₂ : R₂ = I := face_eq_of_le_of_finrank_le R₂ I hR₂.1 hR₂I (by omega)
  exact hne (e₁.trans e₂.symm)

/-- If two compatible local facets `G_u, G_w` of `Q` at vertices `u, w ∈ F` share two distinct
ridges `R₁, R₂ ≤ F` in the `(d - 1)`-skeleton (whose images under `φ` are ridges of `Q`), then
`G_u = G_w`. -/
theorem compatible_local_facets_eq_of_shared_ridges (d : ℕ)
    (P Q : Set (Fin (d + 1) → ℝ))
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (u w : Fin (d + 1) → ℝ)
    (G_u G_w : PolytopeFace Q)
    (hGu : G_u.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_u.val).direction = d)
    (hGw : G_w.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_w.val).direction = d)
    (hUpper_u : ∀ S : SkeletonFace P (d + 1 - 2), u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F))
    (hUpper_w : ∀ S : SkeletonFace P (d + 1 - 2), w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F))
    (R₁ R₂ : SkeletonFace P (d + 1 - 2))
    (hR₁F : R₁.val ≤ F) (hR₂F : R₂.val ≤ F)
    (huR₁ : u ∈ R₁.val.val) (hwR₁ : w ∈ R₁.val.val)
    (huR₂ : u ∈ R₂.val.val) (hwR₂ : w ∈ R₂.val.val)
    (hφR₁ : (φ R₁).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₁).val.val).direction = d - 1)
    (hφR₂ : (φ R₂).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₂).val.val).direction = d - 1)
    (hne : R₁ ≠ R₂) :
    G_u = G_w := by
  have h1u : (φ R₁).val ≤ G_u := (hUpper_u R₁ huR₁).mpr hR₁F
  have h1w : (φ R₁).val ≤ G_w := (hUpper_w R₁ hwR₁).mpr hR₁F
  have h2u : (φ R₂).val ≤ G_u := (hUpper_u R₂ huR₂).mpr hR₂F
  have h2w : (φ R₂).val ≤ G_w := (hUpper_w R₂ hwR₂).mpr hR₂F
  have hneφ : (φ R₁).val ≠ (φ R₂).val := by
    intro hEq
    exact hne (φ.injective (Subtype.ext hEq))
  exact facets_eq_of_two_shared_ridges (d + 1) Q G_u G_w (φ R₁).val (φ R₂).val
    hGu hGw hφR₁ hφR₂ hneφ h1u h1w h2u h2w

end Grunbaum2003Compat

open Grunbaum2003 Grunbaum2003Compat in
theorem solution (d : ℕ) (hd : 3 ≤ d)
    (ih : ∀ (P Q : Set (Fin d → ℝ)), IsDPolytope P → IsDPolytope Q →
      ∀ φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2),
        ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
          ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) :
    (∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
      ∃ G : PolytopeFace Q,
        G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
        (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F))) ∧
    (∀ (u w : Fin (d + 1) → ℝ) (G_u G_w : PolytopeFace Q),
      (G_u.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_u.val).direction = d) →
      (G_w.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_w.val).direction = d) →
      (∀ S : SkeletonFace P (d + 1 - 2), u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
      (∀ S : SkeletonFace P (d + 1 - 2), w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
      ∀ R₁ R₂ : SkeletonFace P (d + 1 - 2),
        R₁.val ≤ F → R₂.val ≤ F →
        u ∈ R₁.val.val → w ∈ R₁.val.val →
        u ∈ R₂.val.val → w ∈ R₂.val.val →
        ((φ R₁).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₁).val.val).direction = d - 1) →
        ((φ R₂).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₂).val.val).direction = d - 1) →
        R₁ ≠ R₂ →
        G_u = G_w) :=
  ⟨fun v hv hvF => exists_compatible_local_facet_at_vertex d hd ih P Q hP hQ φ F hF v hv hvF,
   fun u w G_u G_w hGu hGw hUu hUw R₁ R₂ hR₁F hR₂F huR₁ hwR₁ huR₂ hwR₂ hφR₁ hφR₂ hne =>
     compatible_local_facets_eq_of_shared_ridges d P Q φ F u w G_u G_w hGu hGw hUu hUw
       R₁ R₂ hR₁F hR₂F huR₁ hwR₁ huR₂ hwR₂ hφR₁ hφR₂ hne⟩
