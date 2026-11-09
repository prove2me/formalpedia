-- Prove2me | solution 1 for Grunbaum2003.three_polytope_facet_of_induced_nonseparating_cycle
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:59:08.527134+00:00
-- url     : https://prove2.me/submissions/53ec64aa-03c9-48c8-a2aa-b2cf4d588e51

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
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_three_polytope_facet_is_induced_nonseparating_cycle
import Theorems.Thm_Grunbaum2003_three_polytope_even_cycle_facet_bipartition

set_option autoImplicit false
open Classical

namespace Grunbaum2003CycleToFacet
open Grunbaum2003

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

theorem face_ne_singleton_of_finrank_pos {n : ℕ} {P : Set (Fin n → ℝ)}
    (G : PolytopeFace P) (v : Fin n → ℝ)
    (hpos : 0 < Module.finrank ℝ (affineSpan ℝ G.val).direction) :
    G.val ≠ {v} := by
  intro hEq
  rw [hEq, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

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

def botSkeletonFace {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) : SkeletonFace P k :=
  ⟨⟨∅, isExposed_empty⟩, Or.inl rfl⟩

def atomSkeletonFace {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) (v : Fin n → ℝ)
    (hv : IsExposed ℝ P {v}) : SkeletonFace P k :=
  ⟨⟨{v}, hv⟩, Or.inr (by
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le k)⟩

theorem botSkeletonFace_le {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ} (S : SkeletonFace P k) :
    botSkeletonFace P k ≤ S :=
  Set.empty_subset S.val.val

theorem eq_botSkeletonFace_iff {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ} (S : SkeletonFace P k) :
    S = botSkeletonFace P k ↔ ¬ S.val.val.Nonempty := by
  rw [Set.not_nonempty_iff_eq_empty]
  refine ⟨fun h => by rw [h]; rfl, fun h => ?_⟩
  ext x
  change x ∈ S.val.val ↔ x ∈ (∅ : Set (Fin n → ℝ))
  rw [h]

theorem isBot_iff {n k : ℕ} {P : Set (Fin n → ℝ)} (B : SkeletonFace P k) :
    (∀ X : SkeletonFace P k, B ≤ X) ↔ B = botSkeletonFace P k := by
  refine ⟨fun h => le_antisymm (h (botSkeletonFace P k)) (botSkeletonFace_le B),
    fun h X => by rw [h]; exact botSkeletonFace_le X⟩

theorem atomSkeletonFace_le_iff {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ}
    (v : Fin n → ℝ) (hv : IsExposed ℝ P {v}) (S : SkeletonFace P k) :
    atomSkeletonFace P k v hv ≤ S ↔ v ∈ S.val.val := by
  change ({v} : Set (Fin n → ℝ)) ⊆ S.val.val ↔ v ∈ S.val.val
  exact Set.singleton_subset_iff

theorem eq_bot_or_eq_atomSkeletonFace {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ}
    (v : Fin n → ℝ) (hv : IsExposed ℝ P {v}) (T : SkeletonFace P k)
    (hT : T ≤ atomSkeletonFace P k v hv) :
    T = botSkeletonFace P k ∨ T = atomSkeletonFace P k v hv := by
  by_cases hne : T.val.val.Nonempty
  · right
    apply le_antisymm hT
    rcases hne with ⟨x, hx⟩
    have hxv : x = v := Set.mem_singleton_iff.1 (hT hx)
    subst hxv
    exact (atomSkeletonFace_le_iff x hv T).2 hx
  · left
    exact (eq_botSkeletonFace_iff T).2 hne

theorem isAtom_iff {n k : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (A : SkeletonFace P k) :
    (¬ (∀ X : SkeletonFace P k, A ≤ X) ∧
      ∀ X : SkeletonFace P k, X < A → ∀ Y : SkeletonFace P k, X ≤ Y) ↔
    ∃ (v : Fin n → ℝ) (hv : IsExposed ℝ P {v}), A = atomSkeletonFace P k v hv := by
  constructor
  · rintro ⟨hNotBot, hMin⟩
    rw [isBot_iff, eq_botSkeletonFace_iff, not_not] at hNotBot
    obtain ⟨v, hvA, hvExp⟩ := exists_exposed_vertex_in_face hP A.val hNotBot
    refine ⟨v, hvExp, ?_⟩
    have hle : atomSkeletonFace P k v hvExp ≤ A := (atomSkeletonFace_le_iff v hvExp A).2 hvA
    by_contra hne
    have hlt : atomSkeletonFace P k v hvExp < A := lt_of_le_of_ne hle (Ne.symm hne)
    have hbot := (isBot_iff _).1 (hMin _ hlt)
    have hv_in : v ∈ (atomSkeletonFace P k v hvExp).val.val := Set.mem_singleton v
    rw [hbot] at hv_in
    exact hv_in
  · rintro ⟨v, hvExp, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [isBot_iff, eq_botSkeletonFace_iff, not_not]
      exact Set.singleton_nonempty v
    · intro X hXA
      rw [isBot_iff]
      rcases eq_bot_or_eq_atomSkeletonFace v hvExp X (le_of_lt hXA) with hbot | hEq
      · exact hbot
      · exact False.elim ((ne_of_lt hXA) hEq)

theorem isEdge_iff (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (E : SkeletonFace P 1) :
    (∀ X : SkeletonFace P 1, E ≤ X → X = E) ↔
    (E.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 1) := by
  constructor
  · intro hMax
    have hTop_dim : Module.finrank ℝ (affineSpan ℝ P).direction = 3 := by
      rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
    let TopP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
    have hPne : P.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, direction_affineSpan, vectorSpan_empty, finrank_bot] at hTop_dim
      omega
    have hEne : E.val.val.Nonempty := by
      by_contra hemp
      obtain ⟨v, _, hvExp⟩ := exists_exposed_vertex_in_face hP TopP hPne
      let U : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp
      have hEU : E ≤ U := by
        rw [(eq_botSkeletonFace_iff E).2 hemp]
        exact botSkeletonFace_le U
      have hEq := hMax U hEU
      have hv_in : v ∈ E.val.val := by
        rw [← hEq]; exact Set.mem_singleton v
      exact hemp ⟨v, hv_in⟩
    refine ⟨hEne, ?_⟩
    rcases E.property with hEmpty | hEle
    · rw [hEmpty] at hEne
      exact False.elim (Set.not_nonempty_empty hEne)
    · by_contra hne1
      have hE0 : Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 0 := by omega
      obtain ⟨v, hvE, hvExp⟩ := exists_exposed_vertex_in_face hP E.val hEne
      let V : PolytopeFace P := ⟨{v}, hvExp⟩
      have hV_eq : V = E.val := by
        apply face_eq_of_le_of_finrank_le V E.val (Set.singleton_nonempty v)
          (Set.singleton_subset_iff.2 hvE)
        rw [hE0]; exact Nat.zero_le _
      obtain ⟨g, _, hex_z⟩ := exists_improving_dual_of_finrank_lt E.val TopP v hvE (by
        change Module.finrank ℝ (affineSpan ℝ E.val.val).direction <
          Module.finrank ℝ (affineSpan ℝ P).direction
        omega)
      obtain ⟨G', _, hG'ne, hG'1, _, _, hvG', _, _⟩ :=
        improving_edge_and_global_facet_from_ridge_pairs.1 hP TopP v hvExp (E.val.property.subset hvE) (-g) hex_z
      let U : SkeletonFace P 1 := ⟨G', Or.inr (by omega)⟩
      have hEU : E ≤ U := by
        change E.val.val ⊆ G'.val
        have hVE : E.val.val = {v} := congrArg Subtype.val hV_eq.symm
        rw [hVE]
        exact Set.singleton_subset_iff.2 hvG'
      have hEq := hMax U hEU
      have hDimEq : Module.finrank ℝ (affineSpan ℝ G'.val).direction =
          Module.finrank ℝ (affineSpan ℝ E.val.val).direction := by
        rw [congrArg (fun S : SkeletonFace P 1 => S.val.val) hEq]
      omega
  · rintro ⟨hEne, hE1⟩ X hEX
    have hXne : X.val.val.Nonempty := hEne.mono hEX
    rcases X.property with hEmpty | hXle
    · rw [hEmpty] at hXne
      exact False.elim (Set.not_nonempty_empty hXne)
    · have hEq : E.val = X.val :=
        face_eq_of_le_of_finrank_le E.val X.val hEne hEX (by omega)
      exact Subtype.ext hEq.symm

theorem vertices_eq_of_nonempty_edge_closed {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (K : PolytopeFace P)
    (Good : (Fin n → ℝ) → Prop)
    (hNe : ∃ v₀ ∈ K.val, IsExposed ℝ P {v₀} ∧ Good v₀)
    (hClosed : ∀ (u w : Fin n → ℝ) (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      E ≤ K → IsExposed ℝ P {u} → IsExposed ℝ P {w} →
      u ∈ E.val → w ∈ E.val → Good u → Good w) :
    ∀ v ∈ K.val, IsExposed ℝ P {v} → Good v := by
  intro w hwK hwExp
  by_contra hwBad
  have hFin := (polytope_face_eq_convexHull_exposed_vertices n P hP).1
  let s : Finset (Fin n → ℝ) := hFin.toFinset
  rcases hNe with ⟨v₀, hv₀K, hv₀Exp, hv₀Good⟩
  let A : Finset (Fin n → ℝ) := s.filter (fun v => v ∈ K.val ∧ IsExposed ℝ P {v} ∧ Good v)
  have hv₀s : v₀ ∈ s := hFin.mem_toFinset.2 hv₀Exp
  have hA_ne : A.Nonempty := ⟨v₀, Finset.mem_filter.2 ⟨hv₀s, hv₀K, hv₀Exp, hv₀Good⟩⟩
  obtain ⟨l, hwl⟩ := hwExp (Set.singleton_nonempty w)
  obtain ⟨a, haA, haMax⟩ := A.exists_max_image l hA_ne
  rcases (Finset.mem_filter.1 haA) with ⟨_, haK, haExp, haGood⟩
  have haw_ne : a ≠ w := fun h => hwBad (h ▸ haGood)
  have hw_mem : w ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := hwl ▸ Set.mem_singleton w
  have haP : a ∈ P := haExp.subset (Set.mem_singleton a)
  have hla_lt : l a < l w := by
    refine lt_of_le_of_ne (hw_mem.2 a haP) (fun heq => haw_ne ?_)
    have ha_in_w : a ∈ ({w} : Set (Fin n → ℝ)) := by
      rw [hwl]
      exact ⟨haP, fun y hy => by linarith [hw_mem.2 y hy]⟩
    exact Set.mem_singleton_iff.1 ha_in_w
  obtain ⟨E, b, hEne, hE1, hEK, hbExp, haE, hbE, hlab⟩ :=
    improving_edge_and_global_facet_from_ridge_pairs.1 hP K a haExp haK l ⟨w, hwK, hla_lt⟩
  have hbGood : Good b := hClosed a b E ⟨hEne, hE1⟩ hEK haExp hbExp haE hbE haGood
  have hbK : b ∈ K.val := hEK hbE
  have hbs : b ∈ s := hFin.mem_toFinset.2 hbExp
  have hbA : b ∈ A := Finset.mem_filter.2 ⟨hbs, hbK, hbExp, hbGood⟩
  linarith [haMax b hbA]

theorem exists_facet_at_vertex (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q)
    (w : Fin 3 → ℝ) (hwExp : IsExposed ℝ Q {w}) :
    ∃ F : PolytopeFace Q,
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) ∧ w ∈ F.val := by
  have hTop_dim : Module.finrank ℝ (affineSpan ℝ Q).direction = 3 := by
    rw [hQ.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let TopQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
  have hTopQ_dim : Module.finrank ℝ (affineSpan ℝ TopQ.val).direction = 3 := hTop_dim
  let V : PolytopeFace Q := ⟨{w}, hwExp⟩
  have hV_dim : Module.finrank ℝ (affineSpan ℝ V.val).direction = 0 := by
    change Module.finrank ℝ (affineSpan ℝ ({w} : Set (Fin 3 → ℝ))).direction = 0
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
  obtain ⟨E, hVE, hETop, hEne, hE1⟩ :=
    exists_face_step_up_finrank 0 hQ V TopQ (Set.singleton_nonempty w) hwExp.subset hV_dim (by omega)
  obtain ⟨F, hEF, _, hFne, hF2⟩ :=
    exists_face_step_up_finrank 1 hQ E TopQ hEne hETop hE1 (by omega)
  exact ⟨F, ⟨hFne, hF2⟩, hEF (hVE (Set.mem_singleton w))⟩

theorem exists_facet_above_edge (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q)
    (E : SkeletonFace Q 1)
    (hE : ∀ X : SkeletonFace Q 1, E ≤ X → X = E) :
    ∃ F : PolytopeFace Q,
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) ∧ E.val ≤ F := by
  have hTop_dim : Module.finrank ℝ (affineSpan ℝ Q).direction = 3 := by
    rw [hQ.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let TopQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
  have hTopQ_dim : Module.finrank ℝ (affineSpan ℝ TopQ.val).direction = 3 := hTop_dim
  obtain ⟨hEne, hE1⟩ := (isEdge_iff Q hQ E).1 hE
  obtain ⟨F, hEF, _, hFne, hF2⟩ :=
    exists_face_step_up_finrank 1 hQ E.val TopQ hEne E.val.property.subset hE1 (by omega)
  exact ⟨F, ⟨hFne, hF2⟩, hEF⟩

/-- At any outside vertex `w` (`atomSkeletonFace Q 1 w hwExp ∉ C`), all facets containing `w`
have the same `inSide` value. -/
theorem outside_vertex_facets_same_side (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q)
    (C : Set (SkeletonFace Q 1))
    (hInduced : ∀ S : SkeletonFace Q 1, S ∈ C ↔
      ∀ A : SkeletonFace Q 1,
        (¬ (∀ X : SkeletonFace Q 1, A ≤ X) ∧
          ∀ X : SkeletonFace Q 1, X < A → ∀ Y : SkeletonFace Q 1, X ≤ Y) →
        A ≤ S → A ∈ C)
    (inSide : PolytopeFace Q → Prop)
    (hBipart : ∀ (E : SkeletonFace Q 1) (F₁ F₂ : PolytopeFace Q),
      (∀ X : SkeletonFace Q 1, E ≤ X → X = E) → E ∉ C →
      (F₁.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F₁.val).direction = 2) →
      (F₂.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F₂.val).direction = 2) →
      E.val ≤ F₁ → E.val ≤ F₂ → (inSide F₁ ↔ inSide F₂))
    (w : Fin 3 → ℝ) (hwExp : IsExposed ℝ Q {w})
    (hwOut : atomSkeletonFace Q 1 w hwExp ∉ C)
    (F₁ F₂ : PolytopeFace Q)
    (hF₁ : F₁.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F₁.val).direction = 2)
    (hF₂ : F₂.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F₂.val).direction = 2)
    (hwF₁ : w ∈ F₁.val) (hwF₂ : w ∈ F₂.val) :
    inSide F₁ ↔ inSide F₂ := by
  have hHullQ := polytope_face_eq_convexHull_exposed_vertices 3 Q hQ
  have hCutQ := vertex_figure_face_finrank_and_prescribed_cut 3 Q hQ
  obtain ⟨_, _, Q₀, _, Ψ, _, _, hQ₀, _, _, hΨ_props, _⟩ :=
    skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso.2 3 (by omega) Q hQ hHullQ hCutQ w hwExp
  let TopQ₀ : PolytopeFace Q₀ := ⟨Q₀, IsExposed.refl Q₀⟩
  -- Every edge E of Q containing w is outside C by hInduced
  have hEdgeOut_of_w : ∀ E : SkeletonFace Q 1, w ∈ E.val.val → E ∉ C := by
    intro E hwE hEC
    apply hwOut
    exact (hInduced E).1 hEC (atomSkeletonFace Q 1 w hwExp)
      ((isAtom_iff hQ _).2 ⟨w, hwExp, rfl⟩)
      ((atomSkeletonFace_le_iff w hwExp E).2 hwE)
  -- Helper: any exposed vertex u₀ of Q₀ corresponds via Ψ.symm to an edge E(u₀) of Q at w
  let edgeOfVert₀ (u₀ : Fin 2 → ℝ) (hu₀Exp : IsExposed ℝ Q₀ {u₀}) : SkeletonFace Q 1 :=
    let Vu₀ : PolytopeFace Q₀ := ⟨{u₀}, hu₀Exp⟩
    let E_sub : {H : PolytopeFace Q // w ∈ H.val} := Ψ.symm Vu₀
    ⟨E_sub.val, Or.inr (by
      have hΨE : Ψ E_sub = Vu₀ := Ψ.apply_symm_apply Vu₀
      have hE_ne_w : E_sub.val.val ≠ {w} := by
        intro hEq
        have hEmpty : (Ψ E_sub).val = ∅ := ((hΨ_props E_sub).2.1).mpr hEq
        rw [hΨE] at hEmpty
        change ({u₀} : Set (Fin 2 → ℝ)) = ∅ at hEmpty
        exact Set.not_nonempty_empty (hEmpty ▸ Set.singleton_nonempty u₀)
      have hStep := ((hΨ_props E_sub).2.2 hE_ne_w).2
      have hVu₀_dim : Module.finrank ℝ (affineSpan ℝ Vu₀.val).direction = 0 := by
        change Module.finrank ℝ (affineSpan ℝ ({u₀} : Set (Fin 2 → ℝ))).direction = 0
        rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
      rw [hΨE, hVu₀_dim] at hStep
      omega)⟩
  have hEdgeOfVert₀_props : ∀ (u₀ : Fin 2 → ℝ) (hu₀Exp : IsExposed ℝ Q₀ {u₀}),
      let E := edgeOfVert₀ u₀ hu₀Exp
      (∀ X : SkeletonFace Q 1, E ≤ X → X = E) ∧ w ∈ E.val.val ∧ E ∉ C ∧
      ∀ (F : PolytopeFace Q) (hwF : w ∈ F.val),
        u₀ ∈ (Ψ ⟨F, hwF⟩).val → E.val ≤ F := by
    intro u₀ hu₀Exp
    dsimp only
    let Vu₀ : PolytopeFace Q₀ := ⟨{u₀}, hu₀Exp⟩
    let E_sub : {H : PolytopeFace Q // w ∈ H.val} := Ψ.symm Vu₀
    have hΨE : Ψ E_sub = Vu₀ := Ψ.apply_symm_apply Vu₀
    have hE_ne_w : E_sub.val.val ≠ {w} := by
      intro hEq
      have hEmpty : (Ψ E_sub).val = ∅ := ((hΨ_props E_sub).2.1).mpr hEq
      rw [hΨE] at hEmpty
      change ({u₀} : Set (Fin 2 → ℝ)) = ∅ at hEmpty
      exact Set.not_nonempty_empty (hEmpty ▸ Set.singleton_nonempty u₀)
    have hVu₀_dim : Module.finrank ℝ (affineSpan ℝ Vu₀.val).direction = 0 := by
      change Module.finrank ℝ (affineSpan ℝ ({u₀} : Set (Fin 2 → ℝ))).direction = 0
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    have hE_dim : Module.finrank ℝ (affineSpan ℝ E_sub.val.val).direction = 1 := by
      have hStep := ((hΨ_props E_sub).2.2 hE_ne_w).2
      rw [hΨE, hVu₀_dim] at hStep
      omega
    have hE_edge : ∀ X : SkeletonFace Q 1, edgeOfVert₀ u₀ hu₀Exp ≤ X → X = edgeOfVert₀ u₀ hu₀Exp :=
      (isEdge_iff Q hQ (edgeOfVert₀ u₀ hu₀Exp)).2 ⟨⟨w, E_sub.property⟩, hE_dim⟩
    refine ⟨hE_edge, E_sub.property, hEdgeOut_of_w (edgeOfVert₀ u₀ hu₀Exp) E_sub.property, ?_⟩
    intro F hwF hu₀F
    have hle : Vu₀ ≤ Ψ ⟨F, hwF⟩ := Set.singleton_subset_iff.2 hu₀F
    exact (Ψ.symm_apply_le).2 hle
  -- Now F₁ and F₂ give 1D faces of Q₀, hence contain exposed vertices u₁, u₂ of Q₀
  let F₁_sub : {H : PolytopeFace Q // w ∈ H.val} := ⟨F₁, hwF₁⟩
  let F₂_sub : {H : PolytopeFace Q // w ∈ H.val} := ⟨F₂, hwF₂⟩
  have hF₁_ne_w : F₁.val ≠ {w} := face_ne_singleton_of_finrank_pos F₁ w (by omega)
  have hF₂_ne_w : F₂.val ≠ {w} := face_ne_singleton_of_finrank_pos F₂ w (by omega)
  obtain ⟨hΨF₁_ne, _⟩ := (hΨ_props F₁_sub).2.2 hF₁_ne_w
  obtain ⟨hΨF₂_ne, _⟩ := (hΨ_props F₂_sub).2.2 hF₂_ne_w
  obtain ⟨u₁, hu₁F₁, hu₁Exp⟩ := exists_exposed_vertex_in_face hQ₀ (Ψ F₁_sub) hΨF₁_ne
  obtain ⟨u₂, hu₂F₂, hu₂Exp⟩ := exists_exposed_vertex_in_face hQ₀ (Ψ F₂_sub) hΨF₂_ne
  -- Define Good₀(u₀): every facet F of Q at w with u₀ ∈ Ψ(F) has (inSide F ↔ inSide F₁)
  let Good₀ : (Fin 2 → ℝ) → Prop := fun u₀ =>
    ∀ (F : PolytopeFace Q),
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) →
      ∀ (hwF : w ∈ F.val), u₀ ∈ (Ψ ⟨F, hwF⟩).val → (inSide F ↔ inSide F₁)
  have hu₁Good : Good₀ u₁ := by
    intro F hF hwF hu₁F
    obtain ⟨hE_edge, _, hE_out, hE_le⟩ := hEdgeOfVert₀_props u₁ hu₁Exp
    exact hBipart (edgeOfVert₀ u₁ hu₁Exp) F F₁ hE_edge hE_out hF hF₁
      (hE_le F hwF hu₁F) (hE_le F₁ hwF₁ hu₁F₁)
  have hGood_all : ∀ v₀ ∈ TopQ₀.val, IsExposed ℝ Q₀ {v₀} → Good₀ v₀ := by
    refine vertices_eq_of_nonempty_edge_closed hQ₀ TopQ₀ Good₀
      ⟨u₁, hu₁Exp.subset (Set.mem_singleton u₁), hu₁Exp, hu₁Good⟩ ?_
    intro a₀ b₀ E₀ hE₀_1 _ ha₀Exp hb₀Exp ha₀E₀ hb₀E₀ ha₀Good F hF hwF hb₀F
    -- E₀ is a 1D face of Q₀, so Ψ.symm E₀ is a 2D face (facet) H of Q containing w
    let H_sub : {H : PolytopeFace Q // w ∈ H.val} := Ψ.symm E₀
    let H : PolytopeFace Q := H_sub.val
    have hΨH : Ψ H_sub = E₀ := Ψ.apply_symm_apply E₀
    have hH_ne_w : H.val ≠ {w} := by
      intro hEq
      have hEmpty : (Ψ H_sub).val = ∅ := ((hΨ_props H_sub).2.1).mpr hEq
      rw [hΨH] at hEmpty
      rw [hEmpty] at hE₀_1
      exact Set.not_nonempty_empty hE₀_1.1
    have hH_dim : Module.finrank ℝ (affineSpan ℝ H.val).direction = 2 := by
      have hStep := ((hΨ_props H_sub).2.2 hH_ne_w).2
      rw [hΨH, hE₀_1.2] at hStep
      omega
    have hH_facet : H.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ H.val).direction = 2 :=
      ⟨⟨w, H_sub.property⟩, hH_dim⟩
    have ha₀H : a₀ ∈ (Ψ H_sub).val := by rw [hΨH]; exact ha₀E₀
    have hb₀H : b₀ ∈ (Ψ H_sub).val := by rw [hΨH]; exact hb₀E₀
    have hH_eq_F₁ : inSide H ↔ inSide F₁ := ha₀Good H hH_facet H_sub.property ha₀H
    obtain ⟨hEb_edge, _, hEb_out, hEb_le⟩ := hEdgeOfVert₀_props b₀ hb₀Exp
    have hF_eq_H : inSide F ↔ inSide H :=
      hBipart (edgeOfVert₀ b₀ hb₀Exp) F H hEb_edge hEb_out hF hH_facet
        (hEb_le F hwF hb₀F) (hEb_le H H_sub.property hb₀H)
    exact hF_eq_H.trans hH_eq_F₁
  exact (hGood_all u₂ (hu₂Exp.subset (Set.mem_singleton u₂)) hu₂Exp F₂ hF₂ hwF₂ hu₂F₂).symm

/-- Subgraph uniqueness in a connected 2-regular graph: if `C₀ ⊆ C` are subsets of `SkeletonFace Q 1`
that are both atom-induced, and `C₀` is 2-regular and nonempty while `C` is connected and 2-regular,
then `C₀ = C`. -/
theorem induced_two_regular_subset_eq (Q : Set (Fin 3 → ℝ))
    (C₀ C : Set (SkeletonFace Q 1)) :
    let isBot : SkeletonFace Q 1 → Prop := fun B => ∀ X : SkeletonFace Q 1, B ≤ X
    let isAtom : SkeletonFace Q 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace Q 1, X < A → isBot X
    let isEdge : SkeletonFace Q 1 → Prop := fun E =>
      ∀ X : SkeletonFace Q 1, E ≤ X → X = E
    (∀ A : SkeletonFace Q 1, isAtom A → A ∈ C₀ → A ∈ C) →
    (∀ S : SkeletonFace Q 1, S ∈ C₀ ↔ (∀ A : SkeletonFace Q 1, isAtom A → A ≤ S → A ∈ C₀)) →
    (∀ S : SkeletonFace Q 1, S ∈ C ↔ (∀ A : SkeletonFace Q 1, isAtom A → A ≤ S → A ∈ C)) →
    ((∃ A : SkeletonFace Q 1, isAtom A ∧ A ∈ C₀) ∧
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C₀ →
        ∃ E₁ E₂ : SkeletonFace Q 1,
          isEdge E₁ ∧ isEdge E₂ ∧ E₁ ∈ C₀ ∧ E₂ ∈ C₀ ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
          ∀ E : SkeletonFace Q 1, isEdge E → E ∈ C₀ → A ≤ E → E = E₁ ∨ E = E₂) →
    ((∃ A : SkeletonFace Q 1, isAtom A ∧ A ∈ C) ∧
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C →
        ∃ E₁ E₂ : SkeletonFace Q 1,
          isEdge E₁ ∧ isEdge E₂ ∧ E₁ ∈ C ∧ E₂ ∈ C ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
          ∀ E : SkeletonFace Q 1, isEdge E → E ∈ C → A ≤ E → E = E₁ ∨ E = E₂) →
    (∀ (Good : SkeletonFace Q 1 → Prop),
      (∃ A₀ : SkeletonFace Q 1, isAtom A₀ ∧ A₀ ∈ C ∧ Good A₀) →
      (∀ A B E : SkeletonFace Q 1, isAtom A → isAtom B → isEdge E →
        A ∈ C → B ∈ C → E ∈ C → A ≤ E → B ≤ E → Good A → Good B) →
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C → Good A) →
    ∀ T : SkeletonFace Q 1, T ∈ C₀ ↔ T ∈ C := by
  intro isBot isAtom isEdge hAtomSub hInd₀ hInd hReg₀ hReg hConn
  have hSub : ∀ S : SkeletonFace Q 1, S ∈ C₀ → S ∈ C := by
    intro S hS₀
    exact (hInd S).2 (fun A hA hAS => hAtomSub A hA ((hInd₀ S).1 hS₀ A hA hAS))
  have hAtomsEq : ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C → A ∈ C₀ := by
    rcases hReg₀.1 with ⟨A₀, hA₀_atom, hA₀_C₀⟩
    refine hConn (fun A => A ∈ C₀) ⟨A₀, hA₀_atom, hAtomSub A₀ hA₀_atom hA₀_C₀, hA₀_C₀⟩ ?_
    intro A B E hA_atom hB_atom hE_edge hAC hBC hEC hAE hBE hAC₀
    obtain ⟨E₁, E₂, hE₁_e, hE₂_e, hE₁_C₀, hE₂_C₀, hE₁₂_ne, hAE₁, hAE₂, _⟩ :=
      hReg₀.2 A hA_atom hAC₀
    obtain ⟨F₁, F₂, _, _, _, _, _, _, _, hF_uniq⟩ :=
      hReg.2 A hA_atom hAC
    have hE₁_F := hF_uniq E₁ hE₁_e (hSub E₁ hE₁_C₀) hAE₁
    have hE₂_F := hF_uniq E₂ hE₂_e (hSub E₂ hE₂_C₀) hAE₂
    have hE_F := hF_uniq E hE_edge hEC hAE
    have hE_E₁₂ : E = E₁ ∨ E = E₂ := by
      rcases hE₁_F with rfl | rfl <;> rcases hE₂_F with h2 | h2
      · exact False.elim (hE₁₂_ne h2.symm)
      · subst h2; exact hE_F
      · subst h2; exact hE_F.symm
      · exact False.elim (hE₁₂_ne h2.symm)
    have hEC₀ : E ∈ C₀ := by
      rcases hE_E₁₂ with rfl | rfl
      · exact hE₁_C₀
      · exact hE₂_C₀
    exact (hInd₀ E).1 hEC₀ B hB_atom hBE
  intro T
  refine ⟨hSub T, fun hTC => (hInd₀ T).2 (fun A hA hAT => hAtomsEq A hA ((hInd T).1 hTC A hA hAT))⟩

end Grunbaum2003CycleToFacet

open Grunbaum2003 Grunbaum2003CycleToFacet in
theorem solution
    (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q)
    (C : Set (SkeletonFace Q 1)) :
    let isBot : SkeletonFace Q 1 → Prop := fun B => ∀ X : SkeletonFace Q 1, B ≤ X
    let isAtom : SkeletonFace Q 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace Q 1, X < A → isBot X
    let isEdge : SkeletonFace Q 1 → Prop := fun E =>
      ∀ X : SkeletonFace Q 1, E ≤ X → X = E
    (∀ S : SkeletonFace Q 1, S ∈ C ↔ (∀ A : SkeletonFace Q 1, isAtom A → A ≤ S → A ∈ C)) →
    ((∃ A : SkeletonFace Q 1, isAtom A ∧ A ∈ C) ∧
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C →
        ∃ E₁ E₂ : SkeletonFace Q 1,
          isEdge E₁ ∧ isEdge E₂ ∧ E₁ ∈ C ∧ E₂ ∈ C ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
          ∀ E : SkeletonFace Q 1, isEdge E → E ∈ C → A ≤ E → E = E₁ ∨ E = E₂) →
    (∀ (Good : SkeletonFace Q 1 → Prop),
      (∃ A₀ : SkeletonFace Q 1, isAtom A₀ ∧ A₀ ∈ C ∧ Good A₀) →
      (∀ A B E : SkeletonFace Q 1, isAtom A → isAtom B → isEdge E →
        A ∈ C → B ∈ C → E ∈ C → A ≤ E → B ≤ E → Good A → Good B) →
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C → Good A) →
    ((∃ W : SkeletonFace Q 1, isAtom W ∧ W ∉ C) ∧
      ∀ (Good : SkeletonFace Q 1 → Prop),
        (∃ W₀ : SkeletonFace Q 1, isAtom W₀ ∧ W₀ ∉ C ∧ Good W₀) →
        (∀ U V E : SkeletonFace Q 1, isAtom U → isAtom V → isEdge E →
          U ∉ C → V ∉ C → U ≤ E → V ≤ E → Good U → Good V) →
        ∀ W : SkeletonFace Q 1, isAtom W → W ∉ C → Good W) →
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q 1, T.val ≤ G ↔ T ∈ C := by
  intro isBot isAtom isEdge hInduced hTwoReg hConn hNonsep
  obtain ⟨inSide, ⟨G₁, hG₁_facet, hG₁_in⟩, ⟨G₀, hG₀_facet, hG₀_out⟩, hBipart⟩ :=
    three_polytope_even_cycle_facet_bipartition Q hQ C hInduced hTwoReg hConn hNonsep
  -- Pick an outside atom W₀ and a facet F_W₀ containing W₀ to fix the outside truth value
  rcases hNonsep.1 with ⟨W₀, hW₀_atom, hW₀_out⟩
  obtain ⟨w₀, hw₀Exp, rfl⟩ := (isAtom_iff hQ W₀).1 hW₀_atom
  obtain ⟨F_w₀, hFw₀_facet, hw₀_Fw₀⟩ := exists_facet_at_vertex Q hQ w₀ hw₀Exp
  -- Show that for every outside atom W, every facet F containing W has inSide F ↔ inSide F_w₀
  let GoodOut : SkeletonFace Q 1 → Prop := fun W =>
    ∀ F : PolytopeFace Q,
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) →
      W.val ≤ F → (inSide F ↔ inSide F_w₀)
  have hGoodW₀ : GoodOut (atomSkeletonFace Q 1 w₀ hw₀Exp) := by
    intro F hF hwF_le
    exact outside_vertex_facets_same_side Q hQ C hInduced inSide hBipart
      w₀ hw₀Exp hW₀_out F F_w₀ hF hFw₀_facet (hwF_le (Set.mem_singleton w₀)) hw₀_Fw₀
  have hAllOut : ∀ W : SkeletonFace Q 1, isAtom W → W ∉ C → GoodOut W := by
    refine hNonsep.2 GoodOut ⟨atomSkeletonFace Q 1 w₀ hw₀Exp, hW₀_atom, hW₀_out, hGoodW₀⟩ ?_
    intro U V E hU_atom hV_atom hE_edge hU_out hV_out hUE hVE hUGood F hF hVF
    obtain ⟨v, hvExp, rfl⟩ := (isAtom_iff hQ V).1 hV_atom
    obtain ⟨F_E, hFE_facet, hEFE⟩ := exists_facet_above_edge Q hQ E hE_edge
    have hUF_E : U.val ≤ F_E := le_trans hUE hEFE
    have hVF_E : (atomSkeletonFace Q 1 v hvExp).val ≤ F_E := le_trans hVE hEFE
    have hFE_eq : inSide F_E ↔ inSide F_w₀ := hUGood F_E hFE_facet hUF_E
    have hF_eq_FE : inSide F ↔ inSide F_E :=
      outside_vertex_facets_same_side Q hQ C hInduced inSide hBipart
        v hvExp hV_out F F_E hF hFE_facet (hVF (Set.mem_singleton v)) (hVF_E (Set.mem_singleton v))
    exact hF_eq_FE.trans hFE_eq
  -- Now choose G to have the opposite inSide value from F_w₀
  have hex_G : ∃ G : PolytopeFace Q,
      (G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = 2) ∧
      ¬ (inSide G ↔ inSide F_w₀) := by
    by_cases hSide : inSide F_w₀
    · refine ⟨G₀, hG₀_facet, fun hiff => hG₀_out (hiff.2 hSide)⟩
    · refine ⟨G₁, hG₁_facet, fun hiff => hSide (hiff.1 hG₁_in)⟩
  obtain ⟨G, hG_facet, hG_opp⟩ := hex_G
  refine ⟨G, ?_⟩
  -- Every atom of G lies in C
  have hG_atoms_in_C : ∀ A : SkeletonFace Q 1, isAtom A → A.val ≤ G → A ∈ C := by
    intro A hA_atom hAG
    by_contra hA_out
    exact hG_opp (hAllOut A hA_atom hA_out G hG_facet hAG)
  -- By three_polytope_facet_is_induced_nonseparating_cycle, C₀ = {T | T.val ≤ G} is an induced 2-regular cycle
  obtain ⟨hG_ind, hG_reg, _, _⟩ :=
    three_polytope_facet_is_induced_nonseparating_cycle Q hQ G hG_facet
  exact induced_two_regular_subset_eq Q {T : SkeletonFace Q 1 | T.val ≤ G} C
    hG_atoms_in_C hG_ind hInduced hG_reg hTwoReg hConn
