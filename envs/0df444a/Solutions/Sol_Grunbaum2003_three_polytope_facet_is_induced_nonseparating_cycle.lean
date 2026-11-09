-- Prove2me | solution 1 for Grunbaum2003.three_polytope_facet_is_induced_nonseparating_cycle
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:49:58.432095+00:00
-- url     : https://prove2.me/submissions/c30bf739-e1f2-4d69-9998-9ad1f828d1bc

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

set_option autoImplicit false
open Classical

namespace Grunbaum2003FacetCycle
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

theorem facet_induced (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P) (S : SkeletonFace P 1) :
    S.val ≤ F ↔
      ∀ A : SkeletonFace P 1,
        (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
          ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) →
        A ≤ S → A.val ≤ F := by
  refine ⟨fun hSF A _ hAS => le_trans hAS hSF, fun hAtoms => ?_⟩
  have hHullS := (polytope_face_eq_convexHull_exposed_vertices 3 P hP).2 S.val
  have hHullF := (polytope_face_eq_convexHull_exposed_vertices 3 P hP).2 F
  change S.val.val ⊆ F.val
  rw [hHullS, hHullF]
  refine convexHull_mono (fun v hv => ?_)
  rcases hv with ⟨hvS, hvExp⟩
  let A : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp
  have hA_atom := (isAtom_iff hP A).2 ⟨v, hvExp, rfl⟩
  have hAS : A ≤ S := (atomSkeletonFace_le_iff v hvExp S).2 hvS
  have hAF : A.val ≤ F := hAtoms A hA_atom hAS
  exact ⟨hAF (Set.mem_singleton v), hvExp⟩

theorem facet_two_regular_full (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) :
    (∃ A : SkeletonFace P 1,
      (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) ∧
      A.val ≤ F) ∧
    ∀ A : SkeletonFace P 1,
      (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) →
      A.val ≤ F →
      ∃ E₁ E₂ : SkeletonFace P 1,
        (∀ X : SkeletonFace P 1, E₁ ≤ X → X = E₁) ∧
        (∀ X : SkeletonFace P 1, E₂ ≤ X → X = E₂) ∧
        E₁.val ≤ F ∧ E₂.val ≤ F ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
        ∀ E : SkeletonFace P 1,
          (∀ X : SkeletonFace P 1, E ≤ X → X = E) → E.val ≤ F → A ≤ E → E = E₁ ∨ E = E₂ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v₀, hv₀F, hv₀Exp⟩ := exists_exposed_vertex_in_face hP F hF.1
    refine ⟨atomSkeletonFace P 1 v₀ hv₀Exp,
      (isAtom_iff hP _).2 ⟨v₀, hv₀Exp, rfl⟩,
      Set.singleton_subset_iff.2 hv₀F⟩
  · intro A hA_atom hAF
    obtain ⟨v, hvExp, rfl⟩ := (isAtom_iff hP A).1 hA_atom
    have hvF : v ∈ F.val := hAF (Set.mem_singleton v)
    have hHullP := polytope_face_eq_convexHull_exposed_vertices 3 P hP
    have hCutP := vertex_figure_face_finrank_and_prescribed_cut 3 P hP
    obtain ⟨_, _, Q₀, _, Ψ, _, _, hQ₀, _, _, hΨ_props, _⟩ :=
      skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso.2 3 (by omega) P hP hHullP hCutP v hvExp
    let F_sub : {H : PolytopeFace P // v ∈ H.val} := ⟨F, hvF⟩
    have hF_ne_v : F.val ≠ {v} := face_ne_singleton_of_finrank_pos F v (by omega)
    obtain ⟨hF₀_ne, hF₀_dim_step⟩ := (hΨ_props F_sub).2.2 hF_ne_v
    let F₀ : PolytopeFace Q₀ := Ψ F_sub
    have hF₀_dim : Module.finrank ℝ (affineSpan ℝ F₀.val).direction = 1 := by
      change Module.finrank ℝ (affineSpan ℝ F.val).direction =
        Module.finrank ℝ (affineSpan ℝ F₀.val).direction + 1 at hF₀_dim_step
      omega
    have hHullQ₀ := polytope_face_eq_convexHull_exposed_vertices 2 Q₀ hQ₀
    obtain ⟨a₀, b₀, ha₀Exp, hb₀Exp, hab₀_ne, hF₀_inter, _⟩ :=
      (exposed_edge_pair_and_simplex_faceCount_choose.1 hHullQ₀ F₀.val F₀.property).1 ⟨hF₀_ne, hF₀_dim⟩
    have ha₀_F₀ : a₀ ∈ F₀.val := by
      have hm : a₀ ∈ F₀.val ∩ {x : Fin 2 → ℝ | IsExposed ℝ Q₀ {x}} := by rw [hF₀_inter]; simp
      exact hm.1
    have hb₀_F₀ : b₀ ∈ F₀.val := by
      have hm : b₀ ∈ F₀.val ∩ {x : Fin 2 → ℝ | IsExposed ℝ Q₀ {x}} := by rw [hF₀_inter]; simp
      exact hm.1
    let Va₀ : PolytopeFace Q₀ := ⟨{a₀}, ha₀Exp⟩
    let Vb₀ : PolytopeFace Q₀ := ⟨{b₀}, hb₀Exp⟩
    have hVa₀_dim : Module.finrank ℝ (affineSpan ℝ Va₀.val).direction = 0 := by
      change Module.finrank ℝ (affineSpan ℝ ({a₀} : Set (Fin 2 → ℝ))).direction = 0
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    have hVb₀_dim : Module.finrank ℝ (affineSpan ℝ Vb₀.val).direction = 0 := by
      change Module.finrank ℝ (affineSpan ℝ ({b₀} : Set (Fin 2 → ℝ))).direction = 0
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    let E₁_sub : {H : PolytopeFace P // v ∈ H.val} := Ψ.symm Va₀
    let E₂_sub : {H : PolytopeFace P // v ∈ H.val} := Ψ.symm Vb₀
    have hΨE₁ : Ψ E₁_sub = Va₀ := Ψ.apply_symm_apply Va₀
    have hΨE₂ : Ψ E₂_sub = Vb₀ := Ψ.apply_symm_apply Vb₀
    have hE₁_ne_v : E₁_sub.val.val ≠ {v} := by
      intro hEq
      have hEmpty : (Ψ E₁_sub).val = ∅ := ((hΨ_props E₁_sub).2.1).mpr hEq
      rw [hΨE₁] at hEmpty
      change ({a₀} : Set (Fin 2 → ℝ)) = ∅ at hEmpty
      exact Set.not_nonempty_empty (hEmpty ▸ Set.singleton_nonempty a₀)
    have hE₂_ne_v : E₂_sub.val.val ≠ {v} := by
      intro hEq
      have hEmpty : (Ψ E₂_sub).val = ∅ := ((hΨ_props E₂_sub).2.1).mpr hEq
      rw [hΨE₂] at hEmpty
      change ({b₀} : Set (Fin 2 → ℝ)) = ∅ at hEmpty
      exact Set.not_nonempty_empty (hEmpty ▸ Set.singleton_nonempty b₀)
    have hE₁_dim : Module.finrank ℝ (affineSpan ℝ E₁_sub.val.val).direction = 1 := by
      have hStep := ((hΨ_props E₁_sub).2.2 hE₁_ne_v).2
      rw [hΨE₁, hVa₀_dim] at hStep
      omega
    have hE₂_dim : Module.finrank ℝ (affineSpan ℝ E₂_sub.val.val).direction = 1 := by
      have hStep := ((hΨ_props E₂_sub).2.2 hE₂_ne_v).2
      rw [hΨE₂, hVb₀_dim] at hStep
      omega
    let E₁ : SkeletonFace P 1 := ⟨E₁_sub.val, Or.inr (by omega)⟩
    let E₂ : SkeletonFace P 1 := ⟨E₂_sub.val, Or.inr (by omega)⟩
    have hE₁_edge : ∀ X : SkeletonFace P 1, E₁ ≤ X → X = E₁ :=
      (isEdge_iff P hP E₁).2 ⟨⟨v, E₁_sub.property⟩, hE₁_dim⟩
    have hE₂_edge : ∀ X : SkeletonFace P 1, E₂ ≤ X → X = E₂ :=
      (isEdge_iff P hP E₂).2 ⟨⟨v, E₂_sub.property⟩, hE₂_dim⟩
    have hE₁_F : E₁.val ≤ F := by
      have hle : Va₀ ≤ Ψ F_sub := Set.singleton_subset_iff.2 ha₀_F₀
      exact (Ψ.symm_apply_le).2 hle
    have hE₂_F : E₂.val ≤ F := by
      have hle : Vb₀ ≤ Ψ F_sub := Set.singleton_subset_iff.2 hb₀_F₀
      exact (Ψ.symm_apply_le).2 hle
    have hE₁₂_ne : E₁ ≠ E₂ := by
      intro hEq
      have hValEq : E₁_sub.val = E₂_sub.val :=
        congrArg (fun S : SkeletonFace P 1 => S.val) hEq
      have hSubEq : E₁_sub = E₂_sub := Subtype.ext hValEq
      have hV_eq : Va₀ = Vb₀ := by rw [← hΨE₁, ← hΨE₂, hSubEq]
      have ha₀_in : a₀ ∈ ({b₀} : Set (Fin 2 → ℝ)) := by
        change a₀ ∈ Vb₀.val
        rw [← hV_eq]
        exact Set.mem_singleton a₀
      exact hab₀_ne (Set.mem_singleton_iff.1 ha₀_in)
    refine ⟨E₁, E₂, hE₁_edge, hE₂_edge, hE₁_F, hE₂_F, hE₁₂_ne,
      (atomSkeletonFace_le_iff v hvExp E₁).2 E₁_sub.property,
      (atomSkeletonFace_le_iff v hvExp E₂).2 E₂_sub.property, ?_⟩
    intro E hE_edge hEF hvE_le
    obtain ⟨hE_ne, hE_dim⟩ := (isEdge_iff P hP E).1 hE_edge
    have hvE : v ∈ E.val.val := (atomSkeletonFace_le_iff v hvExp E).1 hvE_le
    let E_sub : {H : PolytopeFace P // v ∈ H.val} := ⟨E.val, hvE⟩
    have hE_ne_v : E.val.val ≠ {v} := face_ne_singleton_of_finrank_pos E.val v (by omega)
    obtain ⟨hE₀_ne, hE₀_dim_step⟩ := (hΨ_props E_sub).2.2 hE_ne_v
    let E₀ : PolytopeFace Q₀ := Ψ E_sub
    have hE₀_dim : Module.finrank ℝ (affineSpan ℝ E₀.val).direction = 0 := by
      change Module.finrank ℝ (affineSpan ℝ E.val.val).direction =
        Module.finrank ℝ (affineSpan ℝ E₀.val).direction + 1 at hE₀_dim_step
      omega
    obtain ⟨w₀, hw₀E₀, hw₀Exp⟩ := exists_exposed_vertex_in_face hQ₀ E₀ hE₀_ne
    let Vw₀ : PolytopeFace Q₀ := ⟨{w₀}, hw₀Exp⟩
    have hVw₀_eq_E₀ : Vw₀ = E₀ := by
      apply face_eq_of_le_of_finrank_le Vw₀ E₀ (Set.singleton_nonempty w₀)
        (Set.singleton_subset_iff.2 hw₀E₀)
      rw [hE₀_dim]; exact Nat.zero_le _
    have hE₀_F₀ : E₀ ≤ F₀ := (Ψ.le_iff_le).2 hEF
    have hw₀_inter : w₀ ∈ F₀.val ∩ {x : Fin 2 → ℝ | IsExposed ℝ Q₀ {x}} :=
      ⟨hE₀_F₀ hw₀E₀, hw₀Exp⟩
    rw [hF₀_inter] at hw₀_inter
    rcases Set.mem_insert_iff.1 hw₀_inter with rfl | hw₀_b₀
    · left
      have hE₀_eq : Ψ E_sub = Ψ E₁_sub := by
        rw [hΨE₁]
        exact hVw₀_eq_E₀.symm
      have hSubEq : E_sub = E₁_sub := Ψ.injective hE₀_eq
      exact Subtype.ext (congrArg (fun X : {H : PolytopeFace P // v ∈ H.val} => X.val) hSubEq)
    · right
      have hw₀_eq_b₀ : w₀ = b₀ := Set.mem_singleton_iff.1 hw₀_b₀
      subst hw₀_eq_b₀
      have hE₀_eq : Ψ E_sub = Ψ E₂_sub := by
        rw [hΨE₂]
        exact hVw₀_eq_E₀.symm
      have hSubEq : E_sub = E₂_sub := Ψ.injective hE₀_eq
      exact Subtype.ext (congrArg (fun X : {H : PolytopeFace P // v ∈ H.val} => X.val) hSubEq)

theorem facet_connected (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P)
    (Good : SkeletonFace P 1 → Prop)
    (hNe : ∃ A₀ : SkeletonFace P 1,
      (¬ (∀ X : SkeletonFace P 1, A₀ ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A₀ → ∀ Y : SkeletonFace P 1, X ≤ Y) ∧
      A₀.val ≤ F ∧ Good A₀)
    (hStep : ∀ A B E : SkeletonFace P 1,
      (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) →
      (¬ (∀ X : SkeletonFace P 1, B ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < B → ∀ Y : SkeletonFace P 1, X ≤ Y) →
      (∀ X : SkeletonFace P 1, E ≤ X → X = E) →
      A.val ≤ F → B.val ≤ F → E.val ≤ F → A ≤ E → B ≤ E → Good A → Good B) :
    ∀ A : SkeletonFace P 1,
      (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) →
      A.val ≤ F → Good A := by
  rcases hNe with ⟨A₀, hA₀_atom, hA₀F, hGoodA₀⟩
  obtain ⟨v₀, hv₀Exp, rfl⟩ := (isAtom_iff hP A₀).1 hA₀_atom
  have hv₀F : v₀ ∈ F.val := hA₀F (Set.mem_singleton v₀)
  let GoodV : (Fin 3 → ℝ) → Prop := fun v =>
    ∀ (hv : IsExposed ℝ P {v}), Good (atomSkeletonFace P 1 v hv)
  have hGoodV_all : ∀ v ∈ F.val, IsExposed ℝ P {v} → GoodV v := by
    refine vertices_eq_of_nonempty_edge_closed hP F GoodV
      ⟨v₀, hv₀F, hv₀Exp, fun _ => hGoodA₀⟩ ?_
    intro u w E hE1 hEF huExp hwExp huE hwE huGoodV hwExp'
    let Au : SkeletonFace P 1 := atomSkeletonFace P 1 u huExp
    let Aw : SkeletonFace P 1 := atomSkeletonFace P 1 w hwExp'
    let E_skel : SkeletonFace P 1 := ⟨E, Or.inr (by omega)⟩
    exact hStep Au Aw E_skel
      ((isAtom_iff hP Au).2 ⟨u, huExp, rfl⟩)
      ((isAtom_iff hP Aw).2 ⟨w, hwExp', rfl⟩)
      ((isEdge_iff P hP E_skel).2 ⟨hE1.1, hE1.2⟩)
      (Set.singleton_subset_iff.2 (hEF huE))
      (Set.singleton_subset_iff.2 (hEF hwE))
      hEF
      ((atomSkeletonFace_le_iff u huExp E_skel).2 huE)
      ((atomSkeletonFace_le_iff w hwExp' E_skel).2 hwE)
      (huGoodV huExp)
  intro A hA_atom hAF
  obtain ⟨v, hvExp, rfl⟩ := (isAtom_iff hP A).1 hA_atom
  exact hGoodV_all v (hAF (Set.mem_singleton v)) hvExp hvExp

theorem outside_pred_on_min_face (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P) (v_F : Fin 3 → ℝ) (hv_F : v_F ∈ F.val)
    (g : StrongDual ℝ (Fin 3 → ℝ))
    (hFg : F.val = {x ∈ P | ∀ y ∈ P, g y ≤ g x})
    (Pred : (Fin 3 → ℝ) → Prop)
    (hNe : ∃ u₀ : Fin 3 → ℝ, u₀ ∉ F.val ∧ IsExposed ℝ P {u₀} ∧ Pred u₀)
    (hClosed : ∀ (u w : Fin 3 → ℝ) (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      IsExposed ℝ P {u} → IsExposed ℝ P {w} →
      u ∉ F.val → w ∉ F.val → u ∈ E.val → w ∈ E.val → Pred u → Pred w) :
    let K_max : PolytopeFace P := ⟨{z ∈ P | ∀ y ∈ P, (-g) y ≤ (-g) z}, fun _ => ⟨-g, rfl⟩⟩
    ∀ z ∈ K_max.val, IsExposed ℝ P {z} → Pred z := by
  intro K_max
  have hvF_mem : v_F ∈ {x ∈ P | ∀ y ∈ P, g y ≤ g x} := hFg ▸ hv_F
  have hg_lt_of_not_mem : ∀ u ∈ P, u ∉ F.val → g u < g v_F := by
    intro u huP huF
    refine lt_of_le_of_ne (hvF_mem.2 u huP) (fun heq => huF ?_)
    rw [hFg]
    exact ⟨huP, fun y hy => by linarith [hvF_mem.2 y hy]⟩
  have hFin := (polytope_face_eq_convexHull_exposed_vertices 3 P hP).1
  let s : Finset (Fin 3 → ℝ) := hFin.toFinset
  rcases hNe with ⟨u₀, hu₀F, hu₀Exp, hu₀Pred⟩
  let A : Finset (Fin 3 → ℝ) := s.filter (fun u => u ∉ F.val ∧ IsExposed ℝ P {u} ∧ Pred u)
  have hu₀s : u₀ ∈ s := hFin.mem_toFinset.2 hu₀Exp
  have hA_ne : A.Nonempty := ⟨u₀, Finset.mem_filter.2 ⟨hu₀s, hu₀F, hu₀Exp, hu₀Pred⟩⟩
  obtain ⟨u_star, hu_star_A, hu_star_max⟩ := A.exists_max_image (-g) hA_ne
  rcases Finset.mem_filter.1 hu_star_A with ⟨_, hu_star_F, hu_star_Exp, hu_star_Pred⟩
  have hu_star_P : u_star ∈ P := hu_star_Exp.subset (Set.mem_singleton u_star)
  have hg_ustar : g u_star < g v_F := hg_lt_of_not_mem u_star hu_star_P hu_star_F
  let TopP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
  have hu_star_Kmax : u_star ∈ K_max.val := by
    refine ⟨hu_star_P, fun y hyP => ?_⟩
    by_contra hlt
    have hex_y : ∃ y ∈ TopP.val, (-g) u_star < (-g) y := ⟨y, hyP, not_le.1 hlt⟩
    obtain ⟨E, b, hEne, hE1, _, hbExp, hu_star_E, hbE, hgb⟩ :=
      improving_edge_and_global_facet_from_ridge_pairs.1 hP TopP u_star hu_star_Exp hu_star_P (-g) hex_y
    have hbP : b ∈ P := hbExp.subset (Set.mem_singleton b)
    have hbF : b ∉ F.val := by
      intro hb_in_F
      have hb_mem : b ∈ {x ∈ P | ∀ y ∈ P, g y ≤ g x} := hFg ▸ hb_in_F
      have hgb_ge : g v_F ≤ g b := hb_mem.2 v_F hvF_mem.1
      change -g u_star < -g b at hgb
      linarith
    have hbPred : Pred b :=
      hClosed u_star b E ⟨hEne, hE1⟩ hu_star_Exp hbExp hu_star_F hbF hu_star_E hbE hu_star_Pred
    have hbs : b ∈ s := hFin.mem_toFinset.2 hbExp
    have hbA : b ∈ A := Finset.mem_filter.2 ⟨hbs, hbF, hbExp, hbPred⟩
    have hle := hu_star_max b hbA
    linarith
  have hKmax_disj : ∀ z ∈ K_max.val, z ∉ F.val := by
    intro z hz hzF
    have hz_mem : z ∈ {x ∈ P | ∀ y ∈ P, g y ≤ g x} := hFg ▸ hzF
    have hgz_ge : g v_F ≤ g z := hz_mem.2 v_F hvF_mem.1
    have hle : (-g) u_star ≤ (-g) z := hz.2 u_star hu_star_P
    change -g u_star ≤ -g z at hle
    linarith
  refine vertices_eq_of_nonempty_edge_closed hP K_max Pred
    ⟨u_star, hu_star_Kmax, hu_star_Exp, hu_star_Pred⟩ ?_
  intro u w E hE1 hEKmax huExp hwExp huE hwE huPred
  exact hClosed u w E hE1 huExp hwExp
    (hKmax_disj u (hEKmax huE)) (hKmax_disj w (hEKmax hwE)) huE hwE huPred

theorem facet_nonseparating (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) :
    (∃ W : SkeletonFace P 1,
      (¬ (∀ X : SkeletonFace P 1, W ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < W → ∀ Y : SkeletonFace P 1, X ≤ Y) ∧
      ¬ W.val ≤ F) ∧
    ∀ (Good : SkeletonFace P 1 → Prop),
      (∃ W₀ : SkeletonFace P 1,
        (¬ (∀ X : SkeletonFace P 1, W₀ ≤ X) ∧
          ∀ X : SkeletonFace P 1, X < W₀ → ∀ Y : SkeletonFace P 1, X ≤ Y) ∧
        ¬ W₀.val ≤ F ∧ Good W₀) →
      (∀ U V E : SkeletonFace P 1,
        (¬ (∀ X : SkeletonFace P 1, U ≤ X) ∧
          ∀ X : SkeletonFace P 1, X < U → ∀ Y : SkeletonFace P 1, X ≤ Y) →
        (¬ (∀ X : SkeletonFace P 1, V ≤ X) ∧
          ∀ X : SkeletonFace P 1, X < V → ∀ Y : SkeletonFace P 1, X ≤ Y) →
        (∀ X : SkeletonFace P 1, E ≤ X → X = E) →
        ¬ U.val ≤ F → ¬ V.val ≤ F → U ≤ E → V ≤ E → Good U → Good V) →
      ∀ W : SkeletonFace P 1,
        (¬ (∀ X : SkeletonFace P 1, W ≤ X) ∧
          ∀ X : SkeletonFace P 1, X < W → ∀ Y : SkeletonFace P 1, X ≤ Y) →
        ¬ W.val ≤ F → Good W := by
  have hTop_dim : Module.finrank ℝ (affineSpan ℝ P).direction = 3 := by
    rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let TopP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
  obtain ⟨v_F, hv_F, hv_F_Exp⟩ := exists_exposed_vertex_in_face hP F hF.1
  obtain ⟨g, hFg⟩ := F.property ⟨v_F, hv_F⟩
  have hvF_mem : v_F ∈ {x ∈ P | ∀ y ∈ P, g y ≤ g x} := hFg ▸ hv_F
  obtain ⟨g', hg'_const, hex_z⟩ := exists_improving_dual_of_finrank_lt F TopP v_F hv_F (by
    change Module.finrank ℝ (affineSpan ℝ F.val).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction
    omega)
  obtain ⟨_, b_out, _, _, _, hb_out_Exp, _, _, hgb_out⟩ :=
    improving_edge_and_global_facet_from_ridge_pairs.1 hP TopP v_F hv_F_Exp (F.property.subset hv_F) (-g') hex_z
  have hb_out_not_F : b_out ∉ F.val := by
    intro hbF
    have heq := hg'_const b_out hbF
    change -g' v_F < -g' b_out at hgb_out
    linarith
  refine ⟨⟨atomSkeletonFace P 1 b_out hb_out_Exp,
    (isAtom_iff hP _).2 ⟨b_out, hb_out_Exp, rfl⟩,
    fun hle => hb_out_not_F (hle (Set.mem_singleton b_out))⟩, ?_⟩
  intro Good ⟨W₀, hW₀_atom, hW₀_not, hGoodW₀⟩ hStep W hW_atom hW_not
  obtain ⟨u₀, hu₀Exp, rfl⟩ := (isAtom_iff hP W₀).1 hW₀_atom
  obtain ⟨w, hwExp, rfl⟩ := (isAtom_iff hP W).1 hW_atom
  have hu₀_not_F : u₀ ∉ F.val := fun hu₀F => hW₀_not (Set.singleton_subset_iff.2 hu₀F)
  have hw_not_F : w ∉ F.val := fun hwF => hW_not (Set.singleton_subset_iff.2 hwF)
  let GoodOut : (Fin 3 → ℝ) → Prop := fun u =>
    ∀ (hu : IsExposed ℝ P {u}), Good (atomSkeletonFace P 1 u hu)
  have hClosedGood : ∀ (u v : Fin 3 → ℝ) (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      IsExposed ℝ P {u} → IsExposed ℝ P {v} →
      u ∉ F.val → v ∉ F.val → u ∈ E.val → v ∈ E.val → GoodOut u → GoodOut v := by
    intro u v E hE1 huExp hvExp huF hvF huE hvE huGood hvExp'
    let Au : SkeletonFace P 1 := atomSkeletonFace P 1 u huExp
    let Av : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp'
    let E_skel : SkeletonFace P 1 := ⟨E, Or.inr (by omega)⟩
    exact hStep Au Av E_skel
      ((isAtom_iff hP Au).2 ⟨u, huExp, rfl⟩)
      ((isAtom_iff hP Av).2 ⟨v, hvExp', rfl⟩)
      ((isEdge_iff P hP E_skel).2 ⟨hE1.1, hE1.2⟩)
      (fun hle => huF (hle (Set.mem_singleton u)))
      (fun hle => hvF (hle (Set.mem_singleton v)))
      ((atomSkeletonFace_le_iff u huExp E_skel).2 huE)
      ((atomSkeletonFace_le_iff v hvExp' E_skel).2 hvE)
      (huGood huExp)
  have hClosedBad : ∀ (u v : Fin 3 → ℝ) (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      IsExposed ℝ P {u} → IsExposed ℝ P {v} →
      u ∉ F.val → v ∉ F.val → u ∈ E.val → v ∈ E.val → ¬ GoodOut u → ¬ GoodOut v := by
    intro u v E hE1 huExp hvExp huF hvF huE hvE huBad hvGood
    exact huBad (hClosedGood v u E hE1 hvExp huExp hvF huF hvE huE hvGood)
  have hKmax_good := outside_pred_on_min_face P hP F v_F hv_F g hFg GoodOut
    ⟨u₀, hu₀_not_F, hu₀Exp, fun _ => hGoodW₀⟩ hClosedGood
  by_contra hwBad
  have hwBadOut : ¬ GoodOut w := fun h => hwBad (h hwExp)
  have hKmax_bad := outside_pred_on_min_face P hP F v_F hv_F g hFg (fun u => ¬ GoodOut u)
    ⟨w, hw_not_F, hwExp, hwBadOut⟩ hClosedBad
  let K_max : PolytopeFace P := ⟨{z ∈ P | ∀ y ∈ P, (-g) y ≤ (-g) z}, fun _ => ⟨-g, rfl⟩⟩
  have hKmax_ne : K_max.val.Nonempty := by
    have hFin := (polytope_face_eq_convexHull_exposed_vertices 3 P hP).1
    let s : Finset (Fin 3 → ℝ) := hFin.toFinset
    have hs_ne : s.Nonempty := ⟨v_F, hFin.mem_toFinset.2 hv_F_Exp⟩
    obtain ⟨z₀, hz₀s, hz₀max⟩ := s.exists_max_image (-g) hs_ne
    have hz₀Exp : IsExposed ℝ P {z₀} := hFin.mem_toFinset.1 hz₀s
    have hz₀P : z₀ ∈ P := hz₀Exp.subset (Set.mem_singleton z₀)
    refine ⟨z₀, hz₀P, fun y hyP => ?_⟩
    have hHullP := (polytope_face_eq_convexHull_exposed_vertices 3 P hP).2 TopP
    change P = convexHull ℝ (P ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}) at hHullP
    have hy_hull : y ∈ convexHull ℝ (s : Set (Fin 3 → ℝ)) := by
      rw [hHullP] at hyP
      refine convexHull_mono (fun x hx => hFin.mem_toFinset.2 hx.2) hyP
    have hsub : (s : Set (Fin 3 → ℝ)) ⊆ {x : Fin 3 → ℝ | (-g) x ≤ (-g) z₀} :=
      fun x hx => hz₀max x hx
    have hconv : Convex ℝ {x : Fin 3 → ℝ | (-g) x ≤ (-g) z₀} :=
      convex_halfSpace_le ((-g : StrongDual ℝ (Fin 3 → ℝ)) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ).isLinear ((-g) z₀)
    exact convexHull_min hsub hconv hy_hull
  obtain ⟨z_star, hz_star_Kmax, hz_star_Exp⟩ := exists_exposed_vertex_in_face hP K_max hKmax_ne
  exact hKmax_bad z_star hz_star_Kmax hz_star_Exp (hKmax_good z_star hz_star_Kmax hz_star_Exp)

end Grunbaum2003FacetCycle

open Grunbaum2003 Grunbaum2003FacetCycle in
theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) :
    let isBot : SkeletonFace P 1 → Prop := fun B => ∀ X : SkeletonFace P 1, B ≤ X
    let isAtom : SkeletonFace P 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace P 1, X < A → isBot X
    let isEdge : SkeletonFace P 1 → Prop := fun E =>
      ∀ X : SkeletonFace P 1, E ≤ X → X = E
    let C : Set (SkeletonFace P 1) := {S : SkeletonFace P 1 | S.val ≤ F}
    (∀ S : SkeletonFace P 1, S ∈ C ↔ (∀ A : SkeletonFace P 1, isAtom A → A ≤ S → A ∈ C)) ∧
    ((∃ A : SkeletonFace P 1, isAtom A ∧ A ∈ C) ∧
      ∀ A : SkeletonFace P 1, isAtom A → A ∈ C →
        ∃ E₁ E₂ : SkeletonFace P 1,
          isEdge E₁ ∧ isEdge E₂ ∧ E₁ ∈ C ∧ E₂ ∈ C ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
          ∀ E : SkeletonFace P 1, isEdge E → E ∈ C → A ≤ E → E = E₁ ∨ E = E₂) ∧
    (∀ (Good : SkeletonFace P 1 → Prop),
      (∃ A₀ : SkeletonFace P 1, isAtom A₀ ∧ A₀ ∈ C ∧ Good A₀) →
      (∀ A B E : SkeletonFace P 1, isAtom A → isAtom B → isEdge E →
        A ∈ C → B ∈ C → E ∈ C → A ≤ E → B ≤ E → Good A → Good B) →
      ∀ A : SkeletonFace P 1, isAtom A → A ∈ C → Good A) ∧
    ((∃ W : SkeletonFace P 1, isAtom W ∧ W ∉ C) ∧
      ∀ (Good : SkeletonFace P 1 → Prop),
        (∃ W₀ : SkeletonFace P 1, isAtom W₀ ∧ W₀ ∉ C ∧ Good W₀) →
        (∀ U V E : SkeletonFace P 1, isAtom U → isAtom V → isEdge E →
          U ∉ C → V ∉ C → U ≤ E → V ≤ E → Good U → Good V) →
        ∀ W : SkeletonFace P 1, isAtom W → W ∉ C → Good W) :=
  ⟨fun S => facet_induced P hP F S,
   facet_two_regular_full P hP F hF,
   fun Good hNe hStep => facet_connected P hP F Good hNe hStep,
   facet_nonseparating P hP F hF⟩
