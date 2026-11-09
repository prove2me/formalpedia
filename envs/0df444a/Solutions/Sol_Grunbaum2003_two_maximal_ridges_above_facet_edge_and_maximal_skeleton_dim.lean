-- Prove2me | solution 1 for Grunbaum2003.two_maximal_ridges_above_facet_edge_and_maximal_skeleton_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:35:58.731116+00:00
-- url     : https://prove2.me/submissions/65656b45-499a-48b7-adbd-f06e474e37ef

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_vertex_figure_face_finrank_and_prescribed_cut
import Theorems.Thm_Grunbaum2003_skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
import Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs

set_option autoImplicit false

namespace Grunbaum2003MaxRidges
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

/-- Every nonempty face of a `d`-polytope contains an exposed vertex of `P`. -/
theorem exists_exposed_vertex_in_face {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (F : PolytopeFace P) (hF : F.val.Nonempty) :
    ∃ v ∈ F.val, IsExposed ℝ P {v} := by
  have hHull := (polytope_face_eq_convexHull_exposed_vertices n P hP).2 F
  have h_inter : (F.val ∩ {x : Fin n → ℝ | IsExposed ℝ P {x}}).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, convexHull_empty] at hHull
    rw [hHull] at hF
    exact Set.not_nonempty_empty hF
  rcases h_inter with ⟨v, hvF, hvExp⟩
  exact ⟨v, hvF, hvExp⟩

/-- A face of positive affine dimension is not a singleton. -/
theorem face_ne_singleton_of_finrank_pos {n : ℕ} {P : Set (Fin n → ℝ)}
    (G : PolytopeFace P) (v : Fin n → ℝ)
    (hpos : 0 < Module.finrank ℝ (affineSpan ℝ G.val).direction) :
    G.val ≠ {v} := by
  intro hEq
  rw [hEq, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

/-- If `G ≤ K` with `finrank G < finrank K` and `v ∈ G`, there is a dual functional `g` constant on
`G` such that `-g` strictly improves from `v` to some point of `K`. -/
theorem exists_improving_dual_of_finrank_lt {n : ℕ} {P : Set (Fin n → ℝ)}
    (G K : PolytopeFace P) (v : Fin n → ℝ) (hvG : v ∈ G.val)
    (hlt : Module.finrank ℝ (affineSpan ℝ G.val).direction <
      Module.finrank ℝ (affineSpan ℝ K.val).direction) :
    ∃ g : StrongDual ℝ (Fin n → ℝ),
      (∀ x ∈ G.val, g x = g v) ∧ (∃ z ∈ K.val, (-g) v < (-g) z) := by
  have hnot_sub : ¬ (K.val ⊆ G.val) := by
    intro hsub
    have hle_dim : Module.finrank ℝ (affineSpan ℝ K.val).direction ≤
        Module.finrank ℝ (affineSpan ℝ G.val).direction := by
      rw [direction_affineSpan, direction_affineSpan]
      exact Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    omega
  obtain ⟨z, hzK, hzG⟩ := Set.not_subset.1 hnot_sub
  obtain ⟨g, hGg⟩ := G.property ⟨v, hvG⟩
  have hv_mem : v ∈ {w ∈ P | ∀ y ∈ P, g y ≤ g w} := hGg ▸ hvG
  have hconst : ∀ x ∈ G.val, g x = g v := by
    intro x hx
    have hx_mem : x ∈ {w ∈ P | ∀ y ∈ P, g y ≤ g w} := hGg ▸ hx
    exact le_antisymm (hv_mem.2 x hx_mem.1) (hx_mem.2 v hv_mem.1)
  have hzP : z ∈ P := K.property.subset hzK
  have hgz_lt : g z < g v := by
    refine lt_of_le_of_ne (hv_mem.2 z hzP) (fun heq => hzG ?_)
    rw [hGg]
    exact ⟨hzP, fun y hy => by linarith [hv_mem.2 y hy]⟩
  refine ⟨g, hconst, z, hzK, ?_⟩
  change -g v < -g z
  linarith

/-- Any nonempty face `G ≤ K` of dimension `r < finrank K` can be stepped up to a face `G'` with
`G ≤ G' ≤ K` of dimension `r + 1`. -/
theorem exists_face_step_up_finrank (r : ℕ) :
    ∀ {n : ℕ} {P : Set (Fin n → ℝ)}, IsDPolytope P →
      ∀ (G K : PolytopeFace P),
        G.val.Nonempty → G ≤ K →
        Module.finrank ℝ (affineSpan ℝ G.val).direction = r →
        r < Module.finrank ℝ (affineSpan ℝ K.val).direction →
        ∃ G' : PolytopeFace P,
          G ≤ G' ∧ G' ≤ K ∧ G'.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ G'.val).direction = r + 1 := by
  induction r with
  | zero =>
    intro n P hP G K hGne hGK hG0 hKpos
    obtain ⟨v, hvG, hvExp⟩ := exists_exposed_vertex_in_face hP G hGne
    let V : PolytopeFace P := ⟨{v}, hvExp⟩
    have hVG : V ≤ G := Set.singleton_subset_iff.2 hvG
    have hV_eq_G : V = G := by
      apply face_eq_of_le_of_finrank_le V G (Set.singleton_nonempty v) hVG
      rw [hG0]
      exact Nat.zero_le _
    obtain ⟨g, _, hex_z⟩ := exists_improving_dual_of_finrank_lt G K v hvG (by omega)
    obtain ⟨E, _, hEne, hE1, hEK, _, hvE, _, _⟩ :=
      improving_edge_and_global_facet_from_ridge_pairs.1 hP K v hvExp (hGK hvG) (-g) hex_z
    have hGE : G ≤ E := by
      rw [← hV_eq_G]
      exact Set.singleton_subset_iff.2 hvE
    exact ⟨E, hGE, hEK, hEne, hE1⟩
  | succ r ih =>
    intro n P hP G K hGne hGK hGr hKgt
    have hK_le_n : Module.finrank ℝ (affineSpan ℝ K.val).direction ≤ n := by
      simpa [Module.finrank_fin_fun] using Submodule.finrank_le (affineSpan ℝ K.val).direction
    have hn : 0 < n := by omega
    obtain ⟨v, hvG, hvExp⟩ := exists_exposed_vertex_in_face hP G hGne
    have hvK : v ∈ K.val := hGK hvG
    have hHull := polytope_face_eq_convexHull_exposed_vertices n P hP
    have hCut := vertex_figure_face_finrank_and_prescribed_cut n P hP
    obtain ⟨_, _, Q₀, _, Ψ, _, _, hQ₀, _, _, hΨ_props, _⟩ :=
      skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso.2 n hn P hP hHull hCut v hvExp
    let G_sub : {H : PolytopeFace P // v ∈ H.val} := ⟨G, hvG⟩
    let K_sub : {H : PolytopeFace P // v ∈ H.val} := ⟨K, hvK⟩
    have hG_ne_v : G.val ≠ {v} := face_ne_singleton_of_finrank_pos G v (by omega)
    have hK_ne_v : K.val ≠ {v} := face_ne_singleton_of_finrank_pos K v (by omega)
    obtain ⟨hΨG_ne, hΨG_dim_step⟩ := (hΨ_props G_sub).2.2 hG_ne_v
    obtain ⟨_, hΨK_dim_step⟩ := (hΨ_props K_sub).2.2 hK_ne_v
    have hΨG_dim : Module.finrank ℝ (affineSpan ℝ (Ψ G_sub).val).direction = r := by
      change Module.finrank ℝ (affineSpan ℝ G.val).direction =
        Module.finrank ℝ (affineSpan ℝ (Ψ G_sub).val).direction + 1 at hΨG_dim_step
      omega
    have hΨK_gt : r < Module.finrank ℝ (affineSpan ℝ (Ψ K_sub).val).direction := by
      change Module.finrank ℝ (affineSpan ℝ K.val).direction =
        Module.finrank ℝ (affineSpan ℝ (Ψ K_sub).val).direction + 1 at hΨK_dim_step
      omega
    have hΨ_le : Ψ G_sub ≤ Ψ K_sub := (Ψ.le_iff_le).2 hGK
    obtain ⟨H₀, hGH₀, hH₀K, hH₀_ne, hH₀_dim⟩ :=
      ih hQ₀ (Ψ G_sub) (Ψ K_sub) hΨG_ne hΨ_le hΨG_dim hΨK_gt
    let G'_sub : {H : PolytopeFace P // v ∈ H.val} := Ψ.symm H₀
    let G' : PolytopeFace P := G'_sub.val
    have hΨG' : Ψ G'_sub = H₀ := Ψ.apply_symm_apply H₀
    have hGG' : G ≤ G' := (Ψ.le_symm_apply).2 hGH₀
    have hG'K : G' ≤ K := (Ψ.symm_apply_le).2 hH₀K
    have hG'_ne_v : G'.val ≠ {v} := by
      intro hEq
      have hEmpty : (Ψ G'_sub).val = ∅ := ((hΨ_props G'_sub).2.1).mpr hEq
      rw [hΨG'] at hEmpty
      rw [hEmpty] at hH₀_ne
      exact Set.not_nonempty_empty hH₀_ne
    have hG'_dim : Module.finrank ℝ (affineSpan ℝ G'.val).direction = r + 1 + 1 := by
      have hStep := ((hΨ_props G'_sub).2.2 hG'_ne_v).2
      rw [hΨG', hH₀_dim] at hStep
      exact hStep
    exact ⟨G', hGG', hG'K, ⟨v, G'_sub.property⟩, hG'_dim⟩

/-- Repeatedly stepping up dimension yields a face `R` with `G ≤ R ≤ K` of any prescribed dimension
`k` between `finrank G` and `finrank K`. -/
theorem exists_face_of_finrank_between {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (G K : PolytopeFace P) (hGne : G.val.Nonempty) (hGK : G ≤ K)
    (k : ℕ)
    (hG_le : Module.finrank ℝ (affineSpan ℝ G.val).direction ≤ k)
    (hk_le : k ≤ Module.finrank ℝ (affineSpan ℝ K.val).direction) :
    ∃ R : PolytopeFace P,
      G ≤ R ∧ R ≤ K ∧ R.val.Nonempty ∧
      Module.finrank ℝ (affineSpan ℝ R.val).direction = k := by
  induction k, hG_le using Nat.le_induction with
  | base => exact ⟨G, le_rfl, hGK, hGne, rfl⟩
  | succ m hm ih =>
    obtain ⟨R₀, hGR₀, hR₀K, hR₀ne, hR₀dim⟩ := ih (by omega)
    obtain ⟨R, hR₀R, hRK, hRne, hRdim⟩ :=
      exists_face_step_up_finrank m hP R₀ K hR₀ne hR₀K hR₀dim (by omega)
    exact ⟨R, le_trans hGR₀ hR₀R, hRK, hRne, hRdim⟩

/-- Any skeleton face in `SkeletonFace P k` of affine dimension `k` is maximal in `SkeletonFace P k`. -/
theorem maximal_skeletonFace_of_finrank_eq {n k : ℕ} {P : Set (Fin n → ℝ)}
    (R : SkeletonFace P k) (hRne : R.val.val.Nonempty)
    (hRdim : Module.finrank ℝ (affineSpan ℝ R.val.val).direction = k) :
    ∀ T : SkeletonFace P k, R ≤ T → T = R := by
  intro T hRT
  have hTne : T.val.val.Nonempty := hRne.mono hRT
  rcases T.property with hEmpty | hTle
  · rw [hEmpty] at hTne
    exact False.elim (Set.not_nonempty_empty hTne)
  · have hEq : R.val = T.val :=
      face_eq_of_le_of_finrank_le R.val T.val hRne hRT (by omega)
    exact Subtype.ext hEq.symm

/-- Every maximal element of `SkeletonFace Q (d + 1 - 2)` for a `(d + 1)`-polytope `Q` (`d ≥ 3`)
is nonempty and has affine dimension `d - 1`. -/
theorem maximal_skeleton_dim (d : ℕ) (hd : 3 ≤ d)
    (Q : Set (Fin (d + 1) → ℝ)) (hQ : IsDPolytope Q)
    (T : SkeletonFace Q (d + 1 - 2))
    (hMax : ∀ U : SkeletonFace Q (d + 1 - 2), T ≤ U → U = T) :
    T.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ T.val.val).direction = d - 1 := by
  have hTop_dim : Module.finrank ℝ (affineSpan ℝ Q).direction = d + 1 := by
    rw [hQ.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let TopQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
  have hQne : Q.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, direction_affineSpan, vectorSpan_empty, finrank_bot] at hTop_dim
    omega
  have hTne : T.val.val.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨v, _, hvExp⟩ := exists_exposed_vertex_in_face hQ TopQ hQne
    let U : SkeletonFace Q (d + 1 - 2) := ⟨⟨{v}, hvExp⟩, Or.inr (by
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
      exact Nat.zero_le _)⟩
    have hTU : T ≤ U := by
      change T.val.val ⊆ {v}
      rw [hemp]
      exact Set.empty_subset _
    have hEq := hMax U hTU
    have hv_in : v ∈ T.val.val := by
      rw [← hEq]
      exact Set.mem_singleton v
    rw [hemp] at hv_in
    exact hv_in
  refine ⟨hTne, ?_⟩
  rcases T.property with hEmpty | hTle
  · rw [hEmpty] at hTne
    exact False.elim (Set.not_nonempty_empty hTne)
  · by_contra hne_dim
    have hlt : Module.finrank ℝ (affineSpan ℝ T.val.val).direction < d - 1 := by omega
    obtain ⟨G', hTG', _, _, hG'dim⟩ :=
      exists_face_step_up_finrank (Module.finrank ℝ (affineSpan ℝ T.val.val).direction)
        hQ T.val TopQ hTne T.val.property.subset rfl (by
          change Module.finrank ℝ (affineSpan ℝ T.val.val).direction <
            Module.finrank ℝ (affineSpan ℝ Q).direction
          omega)
    let U : SkeletonFace Q (d + 1 - 2) := ⟨G', Or.inr (by omega)⟩
    have hEq : U = T := hMax U hTG'
    have hDimEq : Module.finrank ℝ (affineSpan ℝ G'.val).direction =
        Module.finrank ℝ (affineSpan ℝ T.val.val).direction := by
      rw [congrArg (fun S : SkeletonFace Q (d + 1 - 2) => S.val.val) hEq]
    omega

/-- Above every exposed edge `E ≤ F` of a facet `F` of a `(d + 1)`-polytope `P` (`d ≥ 3`), there
exist two distinct maximal elements `R₁ ≠ R₂` of `SkeletonFace P (d + 1 - 2)` below `F`. -/
theorem two_maximal_ridges_above_facet_edge (d : ℕ) (hd : 3 ≤ d)
    (P : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d)
    (E : PolytopeFace P)
    (hE : E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1)
    (hEF : E ≤ F) :
    ∃ R₁ R₂ : SkeletonFace P (d + 1 - 2),
      R₁ ≠ R₂ ∧ R₁.val ≤ F ∧ R₂.val ≤ F ∧ E ≤ R₁.val ∧ E ≤ R₂.val ∧
      (∀ T : SkeletonFace P (d + 1 - 2), R₁ ≤ T → T = R₁) ∧
      (∀ T : SkeletonFace P (d + 1 - 2), R₂ ≤ T → T = R₂) := by
  obtain ⟨v, hvE, hvExp⟩ := exists_exposed_vertex_in_face hP E hE.1
  have hvF : v ∈ F.val := hEF hvE
  have hHull := polytope_face_eq_convexHull_exposed_vertices (d + 1) P hP
  have hCut := vertex_figure_face_finrank_and_prescribed_cut (d + 1) P hP
  obtain ⟨_, _, Q₀, _, Ψ, _, _, hQ₀, _, _, hΨ_props, _⟩ :=
    skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso.2 (d + 1) (by omega) P hP hHull hCut v hvExp
  let E_sub : {H : PolytopeFace P // v ∈ H.val} := ⟨E, hvE⟩
  let F_sub : {H : PolytopeFace P // v ∈ H.val} := ⟨F, hvF⟩
  have hE_ne_v : E.val ≠ {v} := face_ne_singleton_of_finrank_pos E v (by omega)
  have hF_ne_v : F.val ≠ {v} := face_ne_singleton_of_finrank_pos F v (by omega)
  obtain ⟨hE₀_ne, hE₀_dim_step⟩ := (hΨ_props E_sub).2.2 hE_ne_v
  obtain ⟨_, hF₀_dim_step⟩ := (hΨ_props F_sub).2.2 hF_ne_v
  let E₀ : PolytopeFace Q₀ := Ψ E_sub
  let F₀ : PolytopeFace Q₀ := Ψ F_sub
  have hE₀_dim : Module.finrank ℝ (affineSpan ℝ E₀.val).direction = 0 := by
    change Module.finrank ℝ (affineSpan ℝ E.val).direction =
      Module.finrank ℝ (affineSpan ℝ E₀.val).direction + 1 at hE₀_dim_step
    omega
  have hF₀_dim : Module.finrank ℝ (affineSpan ℝ F₀.val).direction = d - 1 := by
    change Module.finrank ℝ (affineSpan ℝ F.val).direction =
      Module.finrank ℝ (affineSpan ℝ F₀.val).direction + 1 at hF₀_dim_step
    omega
  have hE₀F₀ : E₀ ≤ F₀ := (Ψ.le_iff_le).2 hEF
  obtain ⟨R₁₀, hE₀R₁₀, hR₁₀F₀, hR₁₀_ne, hR₁₀_dim⟩ :=
    exists_face_of_finrank_between hQ₀ E₀ F₀ hE₀_ne hE₀F₀ (d - 2) (by omega) (by omega)
  obtain ⟨v₀, hv₀E₀, hv₀Exp⟩ := exists_exposed_vertex_in_face hQ₀ E₀ hE₀_ne
  let V₀ : PolytopeFace Q₀ := ⟨{v₀}, hv₀Exp⟩
  have hV₀_eq_E₀ : V₀ = E₀ := by
    apply face_eq_of_le_of_finrank_le V₀ E₀ (Set.singleton_nonempty v₀)
      (Set.singleton_subset_iff.2 hv₀E₀)
    rw [hE₀_dim]
    exact Nat.zero_le _
  have hv₀R₁₀ : v₀ ∈ R₁₀.val := hE₀R₁₀ hv₀E₀
  obtain ⟨g₁, hg₁_const, hex_z⟩ :=
    exists_improving_dual_of_finrank_lt R₁₀ F₀ v₀ hv₀R₁₀ (by omega)
  obtain ⟨e₂, b₂, he₂_ne, he₂_dim, he₂F₀, _, hv₀e₂, hb₂e₂, hgb₂⟩ :=
    improving_edge_and_global_facet_from_ridge_pairs.1 hQ₀ F₀ v₀ hv₀Exp (hR₁₀F₀ hv₀R₁₀) (-g₁) hex_z
  have hE₀e₂ : E₀ ≤ e₂ := by
    rw [← hV₀_eq_E₀]
    exact Set.singleton_subset_iff.2 hv₀e₂
  have hb₂_not_R₁₀ : b₂ ∉ R₁₀.val := by
    intro hb₂R
    have heq := hg₁_const b₂ hb₂R
    change -g₁ v₀ < -g₁ b₂ at hgb₂
    linarith
  obtain ⟨R₂₀, he₂R₂₀, hR₂₀F₀, hR₂₀_ne, hR₂₀_dim⟩ :=
    exists_face_of_finrank_between hQ₀ e₂ F₀ he₂_ne he₂F₀ (d - 2) (by omega) (by omega)
  have hE₀R₂₀ : E₀ ≤ R₂₀ := le_trans hE₀e₂ he₂R₂₀
  have hR₁₀_ne_R₂₀ : R₁₀ ≠ R₂₀ := by
    intro hEq
    apply hb₂_not_R₁₀
    rw [hEq]
    exact he₂R₂₀ hb₂e₂
  let R₁_sub : {H : PolytopeFace P // v ∈ H.val} := Ψ.symm R₁₀
  let R₂_sub : {H : PolytopeFace P // v ∈ H.val} := Ψ.symm R₂₀
  have hΨR₁ : Ψ R₁_sub = R₁₀ := Ψ.apply_symm_apply R₁₀
  have hΨR₂ : Ψ R₂_sub = R₂₀ := Ψ.apply_symm_apply R₂₀
  have hR₁_ne_v : R₁_sub.val.val ≠ {v} := by
    intro hEq
    have hEmpty : (Ψ R₁_sub).val = ∅ := ((hΨ_props R₁_sub).2.1).mpr hEq
    rw [hΨR₁] at hEmpty
    rw [hEmpty] at hR₁₀_ne
    exact Set.not_nonempty_empty hR₁₀_ne
  have hR₂_ne_v : R₂_sub.val.val ≠ {v} := by
    intro hEq
    have hEmpty : (Ψ R₂_sub).val = ∅ := ((hΨ_props R₂_sub).2.1).mpr hEq
    rw [hΨR₂] at hEmpty
    rw [hEmpty] at hR₂₀_ne
    exact Set.not_nonempty_empty hR₂₀_ne
  have hR₁_dim : Module.finrank ℝ (affineSpan ℝ R₁_sub.val.val).direction = d - 1 := by
    have hStep := ((hΨ_props R₁_sub).2.2 hR₁_ne_v).2
    rw [hΨR₁, hR₁₀_dim] at hStep
    omega
  have hR₂_dim : Module.finrank ℝ (affineSpan ℝ R₂_sub.val.val).direction = d - 1 := by
    have hStep := ((hΨ_props R₂_sub).2.2 hR₂_ne_v).2
    rw [hΨR₂, hR₂₀_dim] at hStep
    omega
  let R₁ : SkeletonFace P (d + 1 - 2) := ⟨R₁_sub.val, Or.inr (by omega)⟩
  let R₂ : SkeletonFace P (d + 1 - 2) := ⟨R₂_sub.val, Or.inr (by omega)⟩
  have hR₁_ne_R₂ : R₁ ≠ R₂ := by
    intro hEq
    have hValEq : R₁_sub.val = R₂_sub.val :=
      congrArg (fun S : SkeletonFace P (d + 1 - 2) => S.val) hEq
    have hSubEq : R₁_sub = R₂_sub := Subtype.ext hValEq
    exact hR₁₀_ne_R₂₀ (by rw [← hΨR₁, ← hΨR₂, hSubEq])
  refine ⟨R₁, R₂, hR₁_ne_R₂, (Ψ.symm_apply_le).2 hR₁₀F₀, (Ψ.symm_apply_le).2 hR₂₀F₀,
    (Ψ.le_symm_apply).2 hE₀R₁₀, (Ψ.le_symm_apply).2 hE₀R₂₀,
    maximal_skeletonFace_of_finrank_eq R₁ ⟨v, R₁_sub.property⟩ (by
      change Module.finrank ℝ (affineSpan ℝ R₁_sub.val.val).direction = d + 1 - 2
      omega),
    maximal_skeletonFace_of_finrank_eq R₂ ⟨v, R₂_sub.property⟩ (by
      change Module.finrank ℝ (affineSpan ℝ R₂_sub.val.val).direction = d + 1 - 2
      omega)⟩

end Grunbaum2003MaxRidges

open Grunbaum2003 Grunbaum2003MaxRidges in
theorem solution (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) :
    (∀ (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      E ≤ F →
      ∃ R₁ R₂ : SkeletonFace P (d + 1 - 2),
        R₁ ≠ R₂ ∧ R₁.val ≤ F ∧ R₂.val ≤ F ∧ E ≤ R₁.val ∧ E ≤ R₂.val ∧
        (∀ T : SkeletonFace P (d + 1 - 2), R₁ ≤ T → T = R₁) ∧
        (∀ T : SkeletonFace P (d + 1 - 2), R₂ ≤ T → T = R₂)) ∧
    (∀ (T : SkeletonFace Q (d + 1 - 2)),
      (∀ U : SkeletonFace Q (d + 1 - 2), T ≤ U → U = T) →
      T.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ T.val.val).direction = d - 1) :=
  ⟨fun E hE hEF => two_maximal_ridges_above_facet_edge d hd P hP F hF E hE hEF,
   fun T hMax => maximal_skeleton_dim d hd Q hQ T hMax⟩
