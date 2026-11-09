-- Prove2me | solution 1 for Grunbaum2003.three_polytope_euler_from_edge_in_two_facets
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T00:44:30.097365+00:00
-- url     : https://prove2.me/submissions/4a24b443-2b1a-4378-974a-699064c5f59d

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs
import Theorems.Thm_Grunbaum2003_three_polytope_facet_is_induced_nonseparating_cycle
import Theorems.Thm_Grunbaum2003_three_polytope_vertex_two_crossings
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Grunbaum2003EulerSketch
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

def botSkeletonFace (P : Set (Fin 3 → ℝ)) (k : ℕ) : SkeletonFace P k :=
  ⟨⟨∅, isExposed_empty⟩, Or.inl rfl⟩

def atomSkeletonFace (P : Set (Fin 3 → ℝ)) (k : ℕ)
    (v : Fin 3 → ℝ) (hv : IsExposed ℝ P {v}) : SkeletonFace P k :=
  ⟨⟨{v}, hv⟩, Or.inr (by
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le k)⟩

theorem isBot_iff {P : Set (Fin 3 → ℝ)}
    (B : SkeletonFace P 1) :
    (∀ X : SkeletonFace P 1, B ≤ X) ↔ B = botSkeletonFace P 1 := by
  constructor
  · intro hAll
    apply Subtype.ext
    apply Subtype.ext
    change B.val.val = ∅
    by_contra hne
    rcases Set.nonempty_iff_ne_empty.2 hne with ⟨x, hx⟩
    exact hAll (botSkeletonFace P 1) hx
  · rintro rfl X
    exact Set.empty_subset _

theorem isAtom_iff {P : Set (Fin 3 → ℝ)} (hP : IsDPolytope P)
    (A : SkeletonFace P 1) :
    (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
      ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y) ↔
    ∃ (v : Fin 3 → ℝ) (hv : IsExposed ℝ P {v}), A = atomSkeletonFace P 1 v hv := by
  simp only [isBot_iff]
  constructor
  · rintro ⟨hneBot, hMin⟩
    have hAne : A.val.val.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hEmpty
      apply hneBot
      exact Subtype.ext (Subtype.ext hEmpty)
    obtain ⟨v, hvA, hvExp⟩ := exists_exposed_vertex_in_face hP A.val hAne
    refine ⟨v, hvExp, ?_⟩
    let V : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp
    have hVA : V ≤ A := Set.singleton_subset_iff.2 hvA
    rcases eq_or_lt_of_le hVA with hEq | hLt
    · exact hEq.symm
    · have hVbot := hMin V hLt
      have hv_empty : v ∈ (∅ : Set (Fin 3 → ℝ)) := by
        change v ∈ (botSkeletonFace P 1).val.val
        rw [← hVbot]
        exact Set.mem_singleton v
      exact False.elim hv_empty
  · rintro ⟨v, hvExp, rfl⟩
    refine ⟨?_, ?_⟩
    · intro hEq
      have hv_empty : v ∈ (∅ : Set (Fin 3 → ℝ)) := by
        change v ∈ (botSkeletonFace P 1).val.val
        rw [← hEq]
        exact Set.mem_singleton v
      exact hv_empty
    · intro X hXA
      have hXsub : X.val.val ⊆ {v} := hXA.1
      rcases Set.subset_singleton_iff_eq.1 hXsub with hEmpty | hSing
      · exact Subtype.ext (Subtype.ext hEmpty)
      · exfalso
        apply hXA.2
        change {v} ⊆ X.val.val
        rw [hSing]

theorem isEdge_iff (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (E : SkeletonFace P 1) :
    (∀ X : SkeletonFace P 1, E ≤ X → X = E) ↔
    (E.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 1) := by
  have hTop_dim : Module.finrank ℝ (affineSpan ℝ P).direction = 3 := by
    rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let TopP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
  have hPne : P.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, direction_affineSpan, vectorSpan_empty, finrank_bot] at hTop_dim
    omega
  constructor
  · intro hMax
    have hEne : E.val.val.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      obtain ⟨v, _, hvExp⟩ := exists_exposed_vertex_in_face hP TopP hPne
      let U : SkeletonFace P 1 := atomSkeletonFace P 1 v hvExp
      have hEU : E ≤ U := by
        change E.val.val ⊆ {v}
        rw [hemp]
        exact Set.empty_subset _
      have hEq := hMax U hEU
      have hv_in : v ∈ E.val.val := by
        rw [← hEq]
        exact Set.mem_singleton v
      rw [hemp] at hv_in
      exact hv_in
    refine ⟨hEne, ?_⟩
    rcases E.property with hEmpty | hEle
    · rw [hEmpty] at hEne
      exact False.elim (Set.not_nonempty_empty hEne)
    · by_contra hne1
      have h0 : Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 0 := by omega
      obtain ⟨v, hvE, hvExp⟩ := exists_exposed_vertex_in_face hP E.val hEne
      let V : PolytopeFace P := ⟨{v}, hvExp⟩
      have hV_eq : V = E.val := by
        apply face_eq_of_le_of_finrank_le V E.val (Set.singleton_nonempty v)
          (Set.singleton_subset_iff.2 hvE)
        rw [h0]
        exact Nat.zero_le _
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

lemma facet_vertex_two_edges_and_degree {P : Set (Fin 3 → ℝ)}
    (hP : IsDPolytope P)
    (V : Finset (Fin 3 → ℝ))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (ℰ : Finset (Set (Fin 3 → ℝ)))
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    {F : Set (Fin 3 → ℝ)}
    (hF : F.Nonempty ∧ IsExposed ℝ P F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    (∀ x ∈ V, x ∈ F →
      ∃ E₁ E₂ : Set (Fin 3 → ℝ),
        E₁ ∈ ℰ ∧ E₂ ∈ ℰ ∧ E₁ ≠ E₂ ∧ x ∈ E₁ ∧ x ∈ E₂ ∧ E₁ ⊆ F ∧ E₂ ⊆ F ∧
        ℰ.filter (fun E => x ∈ E ∧ E ⊆ F) = {E₁, E₂}) ∧
    ∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
      let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
      (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
      ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
        (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)) := by
  have hCycle := three_polytope_facet_is_induced_nonseparating_cycle P hP
    ⟨F, hF.2.1⟩ ⟨hF.1, hF.2.2⟩
  have hTwoEdges : ∀ x ∈ V, x ∈ F →
      ∃ E₁ E₂ : Set (Fin 3 → ℝ),
        E₁ ∈ ℰ ∧ E₂ ∈ ℰ ∧ E₁ ≠ E₂ ∧ x ∈ E₁ ∧ x ∈ E₂ ∧ E₁ ⊆ F ∧ E₂ ⊆ F ∧
        ℰ.filter (fun E => x ∈ E ∧ E ⊆ F) = {E₁, E₂} := by
    intro x hxV hxF
    have hxExp : IsExposed ℝ P {x} := by
      change x ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
      rw [← hV_coe]; exact hxV
    let A : SkeletonFace P 1 := atomSkeletonFace P 1 x hxExp
    have hA_atom : ¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < A → ∀ Y : SkeletonFace P 1, X ≤ Y :=
      (isAtom_iff hP A).2 ⟨x, hxExp, rfl⟩
    have hA_C : A.val ≤ ⟨F, hF.2.1⟩ := Set.singleton_subset_iff.2 hxF
    obtain ⟨E₁, E₂, hE₁_edge, hE₂_edge, hE₁_F, hE₂_F, hE₁₂_ne, hAE₁, hAE₂, hUniq⟩ :=
      hCycle.2.1.2 A hA_atom hA_C
    have hE₁_dim := (isEdge_iff P hP E₁).1 hE₁_edge
    have hE₂_dim := (isEdge_iff P hP E₂).1 hE₂_edge
    have hE₁_mem : E₁.val.val ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hE₁_dim.1, E₁.val.property, hE₁_dim.2⟩
    have hE₂_mem : E₂.val.val ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hE₂_dim.1, E₂.val.property, hE₂_dim.2⟩
    have hE₁₂_val_ne : E₁.val.val ≠ E₂.val.val := by
      intro heq
      exact hE₁₂_ne (Subtype.ext (Subtype.ext heq))
    have hxE₁ : x ∈ E₁.val.val := hAE₁ (Set.mem_singleton x)
    have hxE₂ : x ∈ E₂.val.val := hAE₂ (Set.mem_singleton x)
    refine ⟨E₁.val.val, E₂.val.val, hE₁_mem, hE₂_mem, hE₁₂_val_ne, hxE₁, hxE₂, hE₁_F, hE₂_F, ?_⟩
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hS_mem, hxS, hSF⟩
      have hS_set : S.Nonempty ∧ IsExposed ℝ P S ∧
          Module.finrank ℝ (affineSpan ℝ S).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hS_mem; exact hS_mem
      let ES : SkeletonFace P 1 := ⟨⟨S, hS_set.2.1⟩, Or.inr (le_of_eq hS_set.2.2)⟩
      have hES_edge : ∀ X : SkeletonFace P 1, ES ≤ X → X = ES :=
        (isEdge_iff P hP ES).2 ⟨hS_set.1, hS_set.2.2⟩
      have hAES : A ≤ ES := Set.singleton_subset_iff.2 hxS
      rcases hUniq ES hES_edge hSF hAES with h1 | h2
      · exact Or.inl (congrArg (fun T : SkeletonFace P 1 => T.val.val) h1)
      · exact Or.inr (congrArg (fun T : SkeletonFace P 1 => T.val.val) h2)
    · rintro (rfl | rfl)
      · exact ⟨hE₁_mem, hxE₁, hE₁_F⟩
      · exact ⟨hE₂_mem, hxE₂, hE₂_F⟩
  refine ⟨hTwoEdges, fun l x hxV => ?_⟩
  intro ℰ_x
  by_cases hxF : x ∈ F
  · obtain ⟨E₁, E₂, hE₁_mem, hE₂_mem, hE₁₂_ne, hxE₁, hxE₂, hE₁_F, hE₂_F, hfilt_F⟩ :=
      hTwoEdges x hxV hxF
    have hsub : ℰ_x.filter (fun E => E ⊆ F) ⊆ {E₁, E₂} := by
      rw [← hfilt_F]
      intro E hE
      simp only [Finset.mem_filter, ℰ_x] at hE ⊢
      exact ⟨hE.1.1, hE.1.2.1, hE.2⟩
    have hcard_le2 : (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 := by
      calc (ℰ_x.filter (fun E => E ⊆ F)).card
          ≤ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))).card := Finset.card_le_card hsub
        _ = 2 := Finset.card_pair hE₁₂_ne
    refine ⟨hcard_le2, ?_⟩
    constructor
    · intro hcard2
      have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hE₁₂_ne, hcard2])
      refine ⟨hxF, fun w hwV hwF => ?_⟩
      by_contra hnot_le
      have hlt : l x < l w := lt_of_not_ge hnot_le
      have hxExp : IsExposed ℝ P {x} := by
        change x ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
        rw [← hV_coe]; exact hxV
      obtain ⟨E_up, b, hE_up_ne, hE_up_dim, hE_up_F, hb_exp, hx_E_up, hb_E_up, hl_lt_b⟩ :=
        improving_edge_and_global_facet_from_ridge_pairs.1 hP ⟨F, hF.2.1⟩ x hxExp hxF l ⟨w, hwF, hlt⟩
      have hE_up_mem : E_up.val ∈ ℰ := by
        rw [← Finset.mem_coe, hℰ_coe]
        exact ⟨hE_up_ne, E_up.property, hE_up_dim⟩
      have hE_up_in_pair : E_up.val ∈ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) := by
        rw [← hfilt_F]
        exact Finset.mem_filter.2 ⟨hE_up_mem, hx_E_up, hE_up_F⟩
      rw [← heq_pair] at hE_up_in_pair
      have hE_up_in_x : E_up.val ∈ ℰ_x := (Finset.mem_filter.1 hE_up_in_pair).1
      have hb_V : b ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hb_exp
      have hlb_le : l b ≤ l x := (Finset.mem_filter.1 hE_up_in_x).2.2 b hb_V hb_E_up
      linarith
    · rintro ⟨_, hle_F⟩
      have hpair_sub : ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) ⊆ ℰ_x.filter (fun E => E ⊆ F) := by
        intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        simp only [Finset.mem_filter, ℰ_x]
        rcases hE with rfl | rfl
        · refine ⟨⟨hE₁_mem, hxE₁, fun w hwV hwE => hle_F w hwV (hE₁_F hwE)⟩, hE₁_F⟩
        · refine ⟨⟨hE₂_mem, hxE₂, fun w hwV hwE => hle_F w hwV (hE₂_F hwE)⟩, hE₂_F⟩
      have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
        Finset.Subset.antisymm hsub hpair_sub
      rw [heq_pair, Finset.card_pair hE₁₂_ne]
  · have hemp : ℰ_x.filter (fun E => E ⊆ F) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro E hE hEF
      simp only [Finset.mem_filter, ℰ_x] at hE
      exact hxF (hEF hE.2.1)
    rw [hemp, Finset.card_empty]
    exact ⟨by omega, ⟨by omega, fun h => False.elim (hxF h.1)⟩⟩

lemma exists_linear_separating_pairs {n : ℕ}
    (pairs : Finset ((Fin n → ℝ) × (Fin n → ℝ)))
    (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2) :
    ∃ l : StrongDual ℝ (Fin n → ℝ), ∀ p ∈ pairs, l p.1 ≠ l p.2 := by
  induction pairs using Finset.induction_on with
  | empty => exact ⟨0, fun p hp => by simp at hp⟩
  | @insert p₀ s hp₀ ih =>
    have hp₀_ne : p₀.1 ≠ p₀.2 := hpairs p₀ (Finset.mem_insert_self p₀ s)
    obtain ⟨l', hl'⟩ := ih (fun p hp => hpairs p (Finset.mem_insert_of_mem hp))
    by_cases hl'p₀ : l' p₀.1 ≠ l' p₀.2
    · refine ⟨l', fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hps
      · exact hl'p₀
      · exact hl' p hps
    · have hl'p₀_eq : l' p₀.1 = l' p₀.2 := not_ne_iff.1 hl'p₀
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hp₀_ne
      let m : StrongDual ℝ (Fin n → ℝ) := ContinuousLinearMap.proj i
      have hmp₀ : m p₀.1 ≠ m p₀.2 := hi
      let term : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
        fun p => |m p.1 - m p.2| / |l' p.1 - l' p.2|
      let C : ℝ := 1 + ∑ p ∈ s, term p
      refine ⟨C • l' + m, fun p hp => ?_⟩
      change C * l' p.1 + m p.1 ≠ C * l' p.2 + m p.2
      rcases Finset.mem_insert.1 hp with rfl | hps
      · rw [hl'p₀_eq]
        intro heq
        apply hmp₀
        linarith
      · have hne : l' p.1 - l' p.2 ≠ 0 := sub_ne_zero.2 (hl' p hps)
        have hpos : 0 < |l' p.1 - l' p.2| := abs_pos.2 hne
        have hterm_le : term p ≤ ∑ q ∈ s, term q := by
          refine Finset.single_le_sum (fun q hq => ?_) hps
          dsimp [term]
          positivity
        have hC_gt : |m p.1 - m p.2| / |l' p.1 - l' p.2| < C := by
          change term p < 1 + ∑ q ∈ s, term q
          linarith
        have hC_pos : 0 < C := by
          have h0 : 0 ≤ |m p.1 - m p.2| / |l' p.1 - l' p.2| := by positivity
          linarith
        have hmul : |m p.1 - m p.2| < C * |l' p.1 - l' p.2| :=
          (div_lt_iff₀ hpos).1 hC_gt
        have habs : |C * (l' p.1 - l' p.2)| = C * |l' p.1 - l' p.2| := by
          rw [abs_mul, abs_of_pos hC_pos]
        intro heq
        have heq' : C * (l' p.1 - l' p.2) = -(m p.1 - m p.2) := by linarith
        have habs_eq : |C * (l' p.1 - l' p.2)| = |m p.1 - m p.2| := by
          rw [heq', abs_neg]
        linarith

lemma exists_injective_linear_on_finset {n : ℕ} (V : Finset (Fin n → ℝ)) :
    ∃ l : StrongDual ℝ (Fin n → ℝ), ∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y := by
  let pairs := (V ×ˢ V).filter (fun p => p.1 ≠ p.2)
  obtain ⟨l, hl⟩ := exists_linear_separating_pairs pairs (fun p hp => (Finset.mem_filter.1 hp).2)
  refine ⟨l, fun x hx y hy heq => ?_⟩
  by_contra hne
  exact hl (x, y) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, hne⟩) heq

lemma sum_filter_card_eq_mul_card {α β : Type*} (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [∀ a, DecidablePred (R a)] [∀ b, DecidablePred (fun a => R a b)] (k : ℕ)
    (hB : ∀ b ∈ B, (A.filter (fun a => R a b)).card = k) :
    ∑ a ∈ A, (B.filter (fun b => R a b)).card = k * B.card := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b₀ s hb₀ ih =>
    have hs : ∀ b ∈ s, (A.filter (fun a => R a b)).card = k :=
      fun b hb => hB b (Finset.mem_insert_of_mem hb)
    have hb₀_card : (A.filter (fun a => R a b₀)).card = k :=
      hB b₀ (Finset.mem_insert_self b₀ s)
    have hstep : ∀ a ∈ A,
        ((insert b₀ s).filter (fun b => R a b)).card =
          (if R a b₀ then 1 else 0) + (s.filter (fun b => R a b)).card := by
      intro a _
      rw [Finset.filter_insert]
      split_ifs with hR
      · rw [Finset.card_insert_of_notMem (fun hm => hb₀ (Finset.mem_of_mem_filter b₀ hm))]
        omega
      · omega
    calc ∑ a ∈ A, ((insert b₀ s).filter (fun b => R a b)).card
        = ∑ a ∈ A, ((if R a b₀ then 1 else 0) + (s.filter (fun b => R a b)).card) :=
          Finset.sum_congr rfl hstep
      _ = (∑ a ∈ A, if R a b₀ then 1 else 0) + ∑ a ∈ A, (s.filter (fun b => R a b)).card :=
          Finset.sum_add_distrib
      _ = (A.filter (fun a => R a b₀)).card + k * s.card := by
          rw [← Finset.card_filter, ih hs]
      _ = k * (insert b₀ s).card := by
          rw [hb₀_card, Finset.card_insert_of_notMem hb₀]
          ring

lemma sum_le_two_eq_two_mul_card_two_add_card_one {α : Type*} (s : Finset α) (d : α → ℕ)
    (hd : ∀ x ∈ s, d x ≤ 2) :
    ∑ x ∈ s, d x =
      2 * (s.filter (fun x => d x = 2)).card + (s.filter (fun x => d x = 1)).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ x ∈ s, d x ≤ 2 := fun x hx => hd x (Finset.mem_insert_of_mem hx)
    have hda : d a ≤ 2 := hd a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, ih hs, Finset.filter_insert, Finset.filter_insert]
    have hda_cases : d a = 0 ∨ d a = 1 ∨ d a = 2 := by omega
    rcases hda_cases with h0 | h1 | h2
    · simp [h0]
    · simp [h1, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_of_mem_filter a hm))]
      omega
    · simp [h2, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_of_mem_filter a hm))]
      omega

lemma card_unique_max_on_filter_eq_one {n : ℕ} (V : Finset (Fin n → ℝ))
    (l : StrongDual ℝ (Fin n → ℝ))
    (hl_inj : ∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y)
    (X : Set (Fin n → ℝ))
    [DecidablePred (· ∈ X)]
    [DecidablePred (fun x => x ∈ X ∧ ∀ w ∈ V, w ∈ X → l w ≤ l x)]
    (hX : (V.filter (· ∈ X)).Nonempty) :
    (V.filter (fun x => x ∈ X ∧ ∀ w ∈ V, w ∈ X → l w ≤ l x)).card = 1 := by
  obtain ⟨x₀, hx₀, hmax⟩ := (V.filter (· ∈ X)).exists_max_image l hX
  have hx₀' : x₀ ∈ V ∧ x₀ ∈ X := Finset.mem_filter.1 hx₀
  have hfilt : V.filter (fun x => x ∈ X ∧ ∀ w ∈ V, w ∈ X → l w ≤ l x) = {x₀} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxV, hxX, hle⟩
      have h1 : l x ≤ l x₀ := hmax x (Finset.mem_filter.2 ⟨hxV, hxX⟩)
      have h2 : l x₀ ≤ l x := hle x₀ hx₀'.1 hx₀'.2
      exact hl_inj x hxV x₀ hx₀'.1 (le_antisymm h1 h2)
    · rintro rfl
      exact ⟨hx₀'.1, hx₀'.2, fun w hwV hwX => hmax w (Finset.mem_filter.2 ⟨hwV, hwX⟩)⟩
  rw [hfilt, Finset.card_singleton]

end Grunbaum2003EulerSketch

open Grunbaum2003
open Grunbaum2003EulerSketch

theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2})
    (hTwoFacets : ∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2) :
    V.card + ℱ.card = ℰ.card + 2 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound 3 P
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  have hImpEdge := @Grunbaum2003.improving_edge_and_global_facet_from_ridge_pairs.1 3 P hP
  have hTwoCrossings := Grunbaum2003.three_polytope_vertex_two_crossings
    P hP V ℰ ℱ hV_coe hℰ_coe hℱ_coe hTwoFacets
  let V_set : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
  have hV_fin : V_set.Finite := hHull.1
  have hV_sub_P : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
  have hCardV : faceCount P 0 = V.card := by
    rw [hVBound.1, ← hV_coe, Set.ncard_coe_finset]
  have hV_ge4 : 4 ≤ V.card := by
    rw [← hCardV]
    exact hVBound.2 hP
  have hFacetProp : ∀ F ∈ ℱ,
      ∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
        let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
        (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
        ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
          (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)) := by
    intro F hF
    have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
      rw [← Finset.mem_coe, hℱ_coe] at hF
      exact hF
    exact (facet_vertex_two_edges_and_degree hP V hV_coe ℰ hℰ_coe hF_set).2
  obtain ⟨l, hl_inj⟩ := exists_injective_linear_on_finset V
  have hV_ne : V.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨v_min, hv_min, hl_min⟩ := V.exists_min_image l hV_ne
  obtain ⟨v_max, hv_max, hl_max⟩ := V.exists_max_image l hV_ne
  have hv_min_ne_max : v_min ≠ v_max := by
    intro heq
    have hsub : V ⊆ {v_max} := by
      intro x hx
      rw [Finset.mem_singleton]
      have h1 : l v_min ≤ l x := hl_min x hx
      have h2 : l x ≤ l v_max := hl_max x hx
      rw [heq] at h1
      exact hl_inj x hx v_max hv_max (le_antisymm h2 h1)
    have hcard_le := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard_le
    omega
  let ℰ_x : (Fin 3 → ℝ) → Finset (Set (Fin 3 → ℝ)) :=
    fun x => ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
  let ℱ_x : (Fin 3 → ℝ) → Finset (Set (Fin 3 → ℝ)) :=
    fun x => ℱ.filter (fun F => x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)
  let q : (Fin 3 → ℝ) → ℕ := fun x => (ℰ_x x).card
  let r : (Fin 3 → ℝ) → ℕ := fun x => (ℱ_x x).card
  let c : (Fin 3 → ℝ) → ℕ :=
    fun x => (ℱ.filter (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card = 1)).card
  have hsum_q : ∑ x ∈ V, q x = ℰ.card := by
    have h1 := sum_filter_card_eq_mul_card V ℰ
      (fun x E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x) 1 ?_
    · rw [one_mul] at h1
      exact h1
    · intro E hE
      have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
          Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hE; exact hE
      obtain ⟨a, b, ha, _, _, hEV, _⟩ := (hEdgePair hHull E hE_set.2.1).1 ⟨hE_set.1, hE_set.2.2⟩
      have haV : a ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact ha
      have haE : a ∈ E := by
        have h : a ∈ E ∩ V_set := by rw [hEV]; simp
        exact h.1
      exact card_unique_max_on_filter_eq_one V l hl_inj E ⟨a, Finset.mem_filter.2 ⟨haV, haE⟩⟩
  have hsum_r : ∑ x ∈ V, r x = ℱ.card := by
    have h1 := sum_filter_card_eq_mul_card V ℱ
      (fun x F => x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x) 1 ?_
    · rw [one_mul] at h1
      exact h1
    · intro F hF
      have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
        rw [← Finset.mem_coe, hℱ_coe] at hF; exact hF
      obtain ⟨v₀, hv₀_F, hv₀_exp⟩ := exists_exposed_vertex_in_face hP ⟨F, hF_set.2.1⟩ hF_set.1
      have hv0_V : v₀ ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hv₀_exp
      exact card_unique_max_on_filter_eq_one V l hl_inj F ⟨v₀, Finset.mem_filter.2 ⟨hv0_V, hv₀_F⟩⟩
  have h_double : ∀ x ∈ V, 2 * q x = 2 * r x + c x := by
    intro x hxV
    have h_lhs : ∑ F ∈ ℱ, ((ℰ_x x).filter (fun E => E ⊆ F)).card = 2 * q x :=
      sum_filter_card_eq_mul_card ℱ (ℰ_x x) (fun F E => E ⊆ F) 2
        (fun E hE => hTwoFacets E (Finset.mem_of_mem_filter E hE))
    have h_rhs : ∑ F ∈ ℱ, ((ℰ_x x).filter (fun E => E ⊆ F)).card =
        2 * (ℱ.filter (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card = 2)).card + c x :=
      sum_le_two_eq_two_mul_card_two_add_card_one ℱ
        (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card)
        (fun F hF => (hFacetProp F hF l x hxV).1)
    have h_filt_eq : ℱ.filter (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card = 2) = ℱ_x x := by
      ext F
      simp only [Finset.mem_filter, ℱ_x, and_congr_right_iff]
      intro hF
      exact (hFacetProp F hF l x hxV).2
    rw [h_filt_eq] at h_rhs
    dsimp [r]
    omega
  have h_local_sweep : ∀ x ∈ V,
      1 + r x = q x + (if x = v_min then 1 else 0) + (if x = v_max then 1 else 0) := by
    intro x hxV
    have hd := h_double x hxV
    by_cases hxmin : x = v_min
    · subst x
      have hq_min : q v_min = 0 := by
        dsimp [q, ℰ_x]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro E hE h_in
        have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
            Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
          rw [← Finset.mem_coe, hℰ_coe] at hE; exact hE
        obtain ⟨a, b, ha, hb, hab, hEV, _⟩ := (hEdgePair hHull E hE_set.2.1).1 ⟨hE_set.1, hE_set.2.2⟩
        have haV : a ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact ha
        have hbV : b ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hb
        have haE : a ∈ E := by
          have h : a ∈ E ∩ V_set := by rw [hEV]; simp
          exact h.1
        have hbE : b ∈ E := by
          have h : b ∈ E ∩ V_set := by rw [hEV]; simp
          exact h.1
        by_cases hav : a = v_min
        · subst a
          have h1 : l b ≤ l v_min := h_in.2 b hbV hbE
          have h2 : l v_min ≤ l b := hl_min b hbV
          exact hab (hl_inj v_min hv_min b hbV (le_antisymm h2 h1))
        · have h1 : l a ≤ l v_min := h_in.2 a haV haE
          have h2 : l v_min ≤ l a := hl_min a haV
          exact hav (hl_inj a haV v_min hv_min (le_antisymm h1 h2))
      rw [hq_min] at hd ⊢
      simp only [↓reduceIte, hv_min_ne_max]
      omega
    · by_cases hxmax : x = v_max
      · subst x
        have hc_max : c v_max = 0 := by
          dsimp [c]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro F hF hcard1
          by_cases hvF : v_max ∈ F
          · have hcard2 : ((ℰ_x v_max).filter (fun E => E ⊆ F)).card = 2 :=
              ((hFacetProp F hF l v_max hv_max).2).2 ⟨hvF, fun w hwV _ => hl_max w hwV⟩
            omega
          · have hemp : (ℰ_x v_max).filter (fun E => E ⊆ F) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro E hE hEF
              simp only [Finset.mem_filter, ℰ_x] at hE
              exact hvF (hEF hE.2.1)
            rw [hemp, Finset.card_empty] at hcard1
            omega
        rw [hc_max] at hd
        simp only [hxmin, ↓reduceIte]
        omega
      · have hxExp : IsExposed ℝ P {x} := by
          change x ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
          rw [← hV_coe]; exact hxV
        have hxP : x ∈ P := hV_sub_P hxExp
        have hl_lt_max : l x < l v_max :=
          lt_of_le_of_ne (hl_max x hxV) (fun heq => hxmax (hl_inj x hxV v_max hv_max heq))
        have hl_min_lt : l v_min < l x :=
          lt_of_le_of_ne (hl_min x hxV) (fun heq => hxmin (hl_inj x hxV v_min hv_min heq.symm))
        have hv_max_P : v_max ∈ P := hV_sub_P (by
          change v_max ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
          rw [← hV_coe]; exact hv_max)
        have hv_min_P : v_min ∈ P := hV_sub_P (by
          change v_min ∈ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
          rw [← hV_coe]; exact hv_min)
        obtain ⟨E_up, u_up, hE_up_ne, hE_up_dim, _, hu_up_exp, hx_E_up, hu_E_up, hl_up⟩ :=
          hImpEdge ⟨P, IsExposed.refl P⟩ x hxExp hxP l ⟨v_max, hv_max_P, hl_lt_max⟩
        have hE_up_mem : E_up.val ∈ ℰ := by
          rw [← Finset.mem_coe, hℰ_coe]
          exact ⟨hE_up_ne, E_up.property, hE_up_dim⟩
        have hu_up_V : u_up ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hu_up_exp
        have hmin_neg : (-l) x < (-l) v_min := by
          change -l x < -l v_min; linarith
        obtain ⟨E_dn, u_dn, hE_dn_ne, hE_dn_dim, _, hu_dn_exp, hx_E_dn, hu_dn_E, hl_dn⟩ :=
          hImpEdge ⟨P, IsExposed.refl P⟩ x hxExp hxP (-l) ⟨v_min, hv_min_P, hmin_neg⟩
        have hE_dn_mem : E_dn.val ∈ ℰ := by
          rw [← Finset.mem_coe, hℰ_coe]
          exact ⟨hE_dn_ne, E_dn.property, hE_dn_dim⟩
        have hu_dn_V : u_dn ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hu_dn_exp
        have hl_dn' : l u_dn < l x := by
          change -l x < -l u_dn at hl_dn; linarith
        have hc2 : c x = 2 :=
          hTwoCrossings l hl_inj x hxV
            ⟨E_dn.val, hE_dn_mem, hx_E_dn, u_dn, hu_dn_V, hu_dn_E, hl_dn'⟩
            ⟨E_up.val, hE_up_mem, hx_E_up, u_up, hu_up_V, hu_E_up, hl_up⟩
        rw [hc2] at hd
        simp only [hxmin, hxmax, ↓reduceIte]
        omega
  have hsum_sweep : ∑ x ∈ V, (1 + r x) =
      ∑ x ∈ V, (q x + (if x = v_min then 1 else 0) + (if x = v_max then 1 else 0)) :=
    Finset.sum_congr rfl h_local_sweep
  have hsum_lhs : ∑ x ∈ V, (1 + r x) = V.card + ℱ.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hsum_r]
  have hsum_min : (∑ x ∈ V, if x = v_min then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    have hfilt : V.filter (fun x => x = v_min) = {v_min} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
      rintro rfl; exact hv_min
    rw [hfilt, Finset.card_singleton]
  have hsum_max : (∑ x ∈ V, if x = v_max then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    have hfilt : V.filter (fun x => x = v_max) = {v_max} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
      rintro rfl; exact hv_max
    rw [hfilt, Finset.card_singleton]
  have hsum_rhs : ∑ x ∈ V, (q x + (if x = v_min then 1 else 0) + (if x = v_max then 1 else 0)) =
      ℰ.card + 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_q, hsum_min, hsum_max]
  omega
