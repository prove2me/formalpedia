-- Prove2me | solution 1 for Grunbaum2003.three_polytope_dual_graph_and_euler_relations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T00:36:50.151211+00:00
-- url     : https://prove2.me/submissions/fd0c9b35-eb78-44a9-a9dc-c0bd34ea410b

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
import Theorems.Thm_Grunbaum2003_three_polytope_edge_in_two_facets
import Theorems.Thm_Grunbaum2003_three_polytope_euler_from_edge_in_two_facets

set_option autoImplicit false
open Classical

namespace Grunbaum2003DualEulerSketch
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
  have hbK : b ∈ K.val := hEK hbE
  have hbGood : Good b := hClosed a b E ⟨hEne, hE1⟩ hEK haExp hbExp haE hbE haGood
  have hbs : b ∈ s := hFin.mem_toFinset.2 hbExp
  have hbA : b ∈ A := Finset.mem_filter.2 ⟨hbs, hbK, hbExp, hbGood⟩
  have hba_le : l b ≤ l a := haMax b hbA
  linarith

end Grunbaum2003DualEulerSketch

open Grunbaum2003 Grunbaum2003DualEulerSketch in
theorem solution
    (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q) :
    let isBot : SkeletonFace Q 1 → Prop := fun B => ∀ X : SkeletonFace Q 1, B ≤ X
    let isAtom : SkeletonFace Q 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace Q 1, X < A → isBot X
    let isEdge : SkeletonFace Q 1 → Prop := fun E =>
      ∀ X : SkeletonFace Q 1, E ≤ X → X = E
    let isFacet : PolytopeFace Q → Prop := fun F =>
      F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2
    ∃ (𝒜 ℰ : Finset (SkeletonFace Q 1)) (ℱ : Finset (PolytopeFace Q)),
      (∀ A : SkeletonFace Q 1, A ∈ 𝒜 ↔ isAtom A) ∧
      (∀ E : SkeletonFace Q 1, E ∈ ℰ ↔ isEdge E) ∧
      (∀ F : PolytopeFace Q, F ∈ ℱ ↔ isFacet F) ∧
      (∀ E ∈ ℰ, ∃ F₁ ∈ ℱ, ∃ F₂ ∈ ℱ, F₁ ≠ F₂ ∧ E.val ≤ F₁ ∧ E.val ≤ F₂ ∧
        ∀ F ∈ ℱ, E.val ≤ F → F = F₁ ∨ F = F₂) ∧
      (∀ (GoodF : PolytopeFace Q → Prop),
        (∃ F₀ ∈ ℱ, GoodF F₀) →
        (∀ F₁ ∈ ℱ, ∀ F₂ ∈ ℱ, ∀ E ∈ ℰ, E.val ≤ F₁ → E.val ≤ F₂ → GoodF F₁ → GoodF F₂) →
        ∀ F ∈ ℱ, GoodF F) ∧
      𝒜.card + ℱ.card = ℰ.card + 2 := by
  intro isBot isAtom isEdge isFacet
  have hHull := polytope_face_eq_convexHull_exposed_vertices 3 Q hQ
  let V_set : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | IsExposed ℝ Q {x}}
  have hV_fin : V_set.Finite := hHull.1
  let V : Finset (Fin 3 → ℝ) := hV_fin.toFinset
  have hV_coe : (V : Set (Fin 3 → ℝ)) = V_set := hV_fin.coe_toFinset
  have hFace_fin : ∀ k : ℕ,
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ Q F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k}.Finite := by
    intro k
    refine ((V.powerset.finite_toSet).image
      (fun s : Finset (Fin 3 → ℝ) => convexHull ℝ (s : Set (Fin 3 → ℝ)))).subset ?_
    intro F hF
    refine ⟨V.filter (· ∈ F), ?_, ?_⟩
    · simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      exact Finset.filter_subset _ V
    · symm
      have hFE := hHull.2 ⟨F, hF.2.1⟩
      change F = convexHull ℝ (F ∩ V_set) at hFE
      conv_lhs => rw [hFE]
      congr 1
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
      rw [hV_fin.mem_toFinset]
      exact and_comm
  have hE_fin := hFace_fin 1
  have hF_fin := hFace_fin 2
  let ℰ_set : Finset (Set (Fin 3 → ℝ)) := hE_fin.toFinset
  let ℱ_set : Finset (Set (Fin 3 → ℝ)) := hF_fin.toFinset
  have hℰ_coe : (ℰ_set : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ Q E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1} := hE_fin.coe_toFinset
  have hℱ_coe : (ℱ_set : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ Q F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2} := hF_fin.coe_toFinset
  let mkAtom : {v : Fin 3 → ℝ // v ∈ V} → SkeletonFace Q 1 :=
    fun v => atomSkeletonFace Q 1 v.val (hV_fin.mem_toFinset.1 v.property)
  let mkEdge : {S : Set (Fin 3 → ℝ) // S ∈ ℰ_set} → SkeletonFace Q 1 :=
    fun S => ⟨⟨S.val, (hE_fin.mem_toFinset.1 S.property).2.1⟩,
      Or.inr (le_of_eq (hE_fin.mem_toFinset.1 S.property).2.2)⟩
  let mkFacet : {S : Set (Fin 3 → ℝ) // S ∈ ℱ_set} → PolytopeFace Q :=
    fun S => ⟨S.val, (hF_fin.mem_toFinset.1 S.property).2.1⟩
  let 𝒜 : Finset (SkeletonFace Q 1) := V.attach.image mkAtom
  let ℰ : Finset (SkeletonFace Q 1) := ℰ_set.attach.image mkEdge
  let ℱ : Finset (PolytopeFace Q) := ℱ_set.attach.image mkFacet
  have hmkAtom_inj : Function.Injective mkAtom := by
    intro v₁ v₂ heq
    have hset : ({v₁.val} : Set (Fin 3 → ℝ)) = {v₂.val} :=
      congrArg (fun A : SkeletonFace Q 1 => A.val.val) heq
    exact Subtype.ext (Set.singleton_eq_singleton_iff.1 hset)
  have hmkEdge_inj : Function.Injective mkEdge := by
    intro S₁ S₂ heq
    exact Subtype.ext (congrArg (fun E : SkeletonFace Q 1 => E.val.val) heq)
  have hmkFacet_inj : Function.Injective mkFacet := by
    intro S₁ S₂ heq
    exact Subtype.ext (congrArg (fun F : PolytopeFace Q => F.val) heq)
  have h𝒜_card : 𝒜.card = V.card := by
    rw [Finset.card_image_of_injective _ hmkAtom_inj, Finset.card_attach]
  have hℰ_card : ℰ.card = ℰ_set.card := by
    rw [Finset.card_image_of_injective _ hmkEdge_inj, Finset.card_attach]
  have hℱ_card : ℱ.card = ℱ_set.card := by
    rw [Finset.card_image_of_injective _ hmkFacet_inj, Finset.card_attach]
  have h𝒜 : ∀ A : SkeletonFace Q 1, A ∈ 𝒜 ↔ isAtom A := by
    intro A
    dsimp [isAtom, isBot]
    rw [isAtom_iff hQ A]
    simp only [𝒜, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨v, hvV, rfl⟩
      exact ⟨v, hV_fin.mem_toFinset.1 hvV, rfl⟩
    · rintro ⟨v, hvExp, rfl⟩
      exact ⟨v, hV_fin.mem_toFinset.2 hvExp, rfl⟩
  have hℰ : ∀ E : SkeletonFace Q 1, E ∈ ℰ ↔ isEdge E := by
    intro E
    dsimp [isEdge]
    rw [isEdge_iff Q hQ E]
    simp only [ℰ, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨S, hS, rfl⟩
      have hS' := hE_fin.mem_toFinset.1 hS
      exact ⟨hS'.1, hS'.2.2⟩
    · rintro ⟨hEne, hEdim⟩
      have hS : E.val.val ∈ ℰ_set := hE_fin.mem_toFinset.2 ⟨hEne, E.val.property, hEdim⟩
      refine ⟨E.val.val, hS, Subtype.ext (Subtype.ext rfl)⟩
  have hℱ : ∀ F : PolytopeFace Q, F ∈ ℱ ↔ isFacet F := by
    intro F
    simp only [ℱ, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, isFacet]
    constructor
    · rintro ⟨S, hS, rfl⟩
      have hS' := hF_fin.mem_toFinset.1 hS
      exact ⟨hS'.1, hS'.2.2⟩
    · rintro ⟨hFne, hFdim⟩
      have hS : F.val ∈ ℱ_set := hF_fin.mem_toFinset.2 ⟨hFne, F.property, hFdim⟩
      exact ⟨F.val, hS, Subtype.ext rfl⟩
  have hTwoFacets := three_polytope_edge_in_two_facets Q hQ V ℰ_set ℱ_set hV_coe hℰ_coe hℱ_coe
  have hEuler_set := three_polytope_euler_from_edge_in_two_facets Q hQ V ℰ_set ℱ_set
    hV_coe hℰ_coe hℱ_coe hTwoFacets
  have hDiamond : ∀ E ∈ ℰ, ∃ F₁ ∈ ℱ, ∃ F₂ ∈ ℱ, F₁ ≠ F₂ ∧ E.val ≤ F₁ ∧ E.val ≤ F₂ ∧
      ∀ F ∈ ℱ, E.val ≤ F → F = F₁ ∨ F = F₂ := by
    intro E hE
    obtain ⟨hEne, hEdim⟩ := (isEdge_iff Q hQ E).1 ((hℰ E).1 hE)
    have hE_set : E.val.val ∈ ℰ_set := hE_fin.mem_toFinset.2 ⟨hEne, E.val.property, hEdim⟩
    have hcard2 := hTwoFacets E.val.val hE_set
    obtain ⟨S₁, S₂, hS₁₂_ne, hfilt⟩ := Finset.card_eq_two.1 hcard2
    have hS₁_in : S₁ ∈ ℱ_set.filter (fun S => E.val.val ⊆ S) := by rw [hfilt]; simp
    have hS₂_in : S₂ ∈ ℱ_set.filter (fun S => E.val.val ⊆ S) := by rw [hfilt]; simp
    rcases Finset.mem_filter.1 hS₁_in with ⟨hS₁_mem, hES₁⟩
    rcases Finset.mem_filter.1 hS₂_in with ⟨hS₂_mem, hES₂⟩
    have hS₁' := hF_fin.mem_toFinset.1 hS₁_mem
    have hS₂' := hF_fin.mem_toFinset.1 hS₂_mem
    let F₁ : PolytopeFace Q := ⟨S₁, hS₁'.2.1⟩
    let F₂ : PolytopeFace Q := ⟨S₂, hS₂'.2.1⟩
    have hF₁_mem : F₁ ∈ ℱ := (hℱ F₁).2 ⟨hS₁'.1, hS₁'.2.2⟩
    have hF₂_mem : F₂ ∈ ℱ := (hℱ F₂).2 ⟨hS₂'.1, hS₂'.2.2⟩
    have hF₁₂_ne : F₁ ≠ F₂ := fun heq => hS₁₂_ne (congrArg Subtype.val heq)
    refine ⟨F₁, hF₁_mem, F₂, hF₂_mem, hF₁₂_ne, hES₁, hES₂, ?_⟩
    intro F hF hEF
    have hF_facet := (hℱ F).1 hF
    have hF_set : F.val ∈ ℱ_set := hF_fin.mem_toFinset.2 ⟨hF_facet.1, F.property, hF_facet.2⟩
    have hF_in : F.val ∈ ℱ_set.filter (fun S => E.val.val ⊆ S) :=
      Finset.mem_filter.2 ⟨hF_set, hEF⟩
    rw [hfilt, Finset.mem_insert, Finset.mem_singleton] at hF_in
    rcases hF_in with h1 | h2
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h2)
  have hDualConn : ∀ (GoodF : PolytopeFace Q → Prop),
      (∃ F₀ ∈ ℱ, GoodF F₀) →
      (∀ F₁ ∈ ℱ, ∀ F₂ ∈ ℱ, ∀ E ∈ ℰ, E.val ≤ F₁ → E.val ≤ F₂ → GoodF F₁ → GoodF F₂) →
      ∀ F ∈ ℱ, GoodF F := by
    intro GoodF ⟨F₀, hF₀_mem, hF₀_good⟩ hStepF
    have hCut := vertex_figure_face_finrank_and_prescribed_cut 3 Q hQ
    -- Step 1: At any exposed vertex v of Q, if one incident facet is GoodF, all incident facets are GoodF
    have hLocalFan : ∀ (v : Fin 3 → ℝ), IsExposed ℝ Q {v} →
        ∀ F₁ ∈ ℱ, v ∈ F₁.val → GoodF F₁ →
        ∀ F₂ ∈ ℱ, v ∈ F₂.val → GoodF F₂ := by
      intro v hvExp F₁ hF₁_mem hvF₁ hF₁_good F₂ hF₂_mem hvF₂
      obtain ⟨_, _, Q₀, _, Ψ, _, _, hQ₀, _, _, hΨ_props, _⟩ :=
        skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso.2 3 (by omega) Q hQ hHull hCut v hvExp
      let TopQ₀ : PolytopeFace Q₀ := ⟨Q₀, IsExposed.refl Q₀⟩
      have h_edge_of_vert₀ : ∀ (u₀ : Fin (3 - 1) → ℝ) (hu₀Exp : IsExposed ℝ Q₀ {u₀}),
          let V_u₀ : PolytopeFace Q₀ := ⟨{u₀}, hu₀Exp⟩
          let E_sub := Ψ.symm V_u₀
          ∃ E_skel : SkeletonFace Q 1, E_skel ∈ ℰ ∧ E_skel.val = E_sub.val ∧
            ∀ (H : PolytopeFace Q) (hvH : v ∈ H.val),
              E_skel.val ≤ H ↔ u₀ ∈ (Ψ ⟨H, hvH⟩).val := by
        intro u₀ hu₀Exp V_u₀ E_sub
        have hΨE : Ψ E_sub = V_u₀ := Ψ.apply_symm_apply V_u₀
        have hE_ne_v : E_sub.val.val ≠ {v} := by
          intro heq
          have hemp : (Ψ E_sub).val = ∅ := ((hΨ_props E_sub).2.1).mpr heq
          rw [hΨE] at hemp
          exact Set.singleton_ne_empty u₀ hemp
        have hStep := ((hΨ_props E_sub).2.2 hE_ne_v).2
        have hV_dim : Module.finrank ℝ (affineSpan ℝ V_u₀.val).direction = 0 := by
          change Module.finrank ℝ (affineSpan ℝ ({u₀} : Set (Fin (3 - 1) → ℝ))).direction = 0
          rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
        rw [hΨE, hV_dim] at hStep
        let E_skel : SkeletonFace Q 1 := ⟨E_sub.val, Or.inr (le_of_eq hStep)⟩
        have hE_mem : E_skel ∈ ℰ := (hℰ E_skel).2 ((isEdge_iff Q hQ E_skel).2 ⟨⟨v, E_sub.property⟩, hStep⟩)
        refine ⟨E_skel, hE_mem, rfl, fun H hvH => ?_⟩
        have hle_iff : E_sub ≤ ⟨H, hvH⟩ ↔ V_u₀ ≤ Ψ ⟨H, hvH⟩ := Ψ.symm_apply_le
        change E_sub.val ≤ H ↔ u₀ ∈ (Ψ ⟨H, hvH⟩).val
        rw [← Set.singleton_subset_iff]
        exact hle_iff
      have h_facet_of_edge₀ : ∀ (e₀ : PolytopeFace Q₀),
          (e₀.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ e₀.val).direction = 1) →
          let F_sub := Ψ.symm e₀
          F_sub.val ∈ ℱ ∧ Ψ F_sub = e₀ := by
        intro e₀ ⟨he₀_ne, he₀_dim⟩ F_sub
        have hΨF : Ψ F_sub = e₀ := Ψ.apply_symm_apply e₀
        have hF_ne_v : F_sub.val.val ≠ {v} := by
          intro heq
          have hemp : (Ψ F_sub).val = ∅ := ((hΨ_props F_sub).2.1).mpr heq
          rw [hΨF] at hemp
          rw [hemp] at he₀_ne
          exact Set.not_nonempty_empty he₀_ne
        have hStep := ((hΨ_props F_sub).2.2 hF_ne_v).2
        rw [hΨF, he₀_dim] at hStep
        exact ⟨(hℱ F_sub.val).2 ⟨⟨v, F_sub.property⟩, hStep⟩, hΨF⟩
      let GoodV₀ : (Fin (3 - 1) → ℝ) → Prop := fun u₀ =>
        ∃ (F : PolytopeFace Q) (hvF : v ∈ F.val),
          F ∈ ℱ ∧ u₀ ∈ (Ψ ⟨F, hvF⟩).val ∧ GoodF F
      have hF₁_facet := (hℱ F₁).1 hF₁_mem
      have hF₁_ne_v : F₁.val ≠ {v} := face_ne_singleton_of_finrank_pos F₁ v (by omega)
      have hΨF₁_ne : (Ψ ⟨F₁, hvF₁⟩).val.Nonempty := ((hΨ_props ⟨F₁, hvF₁⟩).2.2 hF₁_ne_v).1
      obtain ⟨u₀₁, hu₀₁_in, hu₀₁_exp⟩ := exists_exposed_vertex_in_face hQ₀ (Ψ ⟨F₁, hvF₁⟩) hΨF₁_ne
      have hGoodV₀_all : ∀ u₀ ∈ TopQ₀.val, IsExposed ℝ Q₀ {u₀} → GoodV₀ u₀ := by
        refine vertices_eq_of_nonempty_edge_closed hQ₀ TopQ₀ GoodV₀
          ⟨u₀₁, hu₀₁_exp.subset (Set.mem_singleton u₀₁), hu₀₁_exp, F₁, hvF₁, hF₁_mem, hu₀₁_in, hF₁_good⟩ ?_
        intro u₀ w₀ e₀ he₀ _ hu₀Exp hw₀Exp hu₀_e₀ hw₀_e₀ ⟨Fa, hvFa, hFa_mem, hu₀_Fa, hFa_good⟩
        obtain ⟨Fb_mem, hΨFb⟩ := h_facet_of_edge₀ e₀ he₀
        let Fb_sub := Ψ.symm e₀
        obtain ⟨E_skel, hE_mem, _, hE_le⟩ := h_edge_of_vert₀ u₀ hu₀Exp
        have hE_Fa : E_skel.val ≤ Fa := (hE_le Fa hvFa).2 hu₀_Fa
        have hE_Fb : E_skel.val ≤ Fb_sub.val := by
          apply (hE_le Fb_sub.val Fb_sub.property).2
          rw [hΨFb]
          exact hu₀_e₀
        have hFb_good : GoodF Fb_sub.val := hStepF Fa hFa_mem Fb_sub.val Fb_mem E_skel hE_mem hE_Fa hE_Fb hFa_good
        refine ⟨Fb_sub.val, Fb_sub.property, Fb_mem, ?_, hFb_good⟩
        rw [hΨFb]
        exact hw₀_e₀
      have hF₂_facet := (hℱ F₂).1 hF₂_mem
      have hF₂_ne_v : F₂.val ≠ {v} := face_ne_singleton_of_finrank_pos F₂ v (by omega)
      have hΨF₂_ne : (Ψ ⟨F₂, hvF₂⟩).val.Nonempty := ((hΨ_props ⟨F₂, hvF₂⟩).2.2 hF₂_ne_v).1
      obtain ⟨u₀₂, hu₀₂_in, hu₀₂_exp⟩ := exists_exposed_vertex_in_face hQ₀ (Ψ ⟨F₂, hvF₂⟩) hΨF₂_ne
      obtain ⟨Fa, hvFa, hFa_mem, hu₀₂_Fa, hFa_good⟩ :=
        hGoodV₀_all u₀₂ (hu₀₂_exp.subset (Set.mem_singleton u₀₂)) hu₀₂_exp
      obtain ⟨E_skel, hE_mem, _, hE_le⟩ := h_edge_of_vert₀ u₀₂ hu₀₂_exp
      exact hStepF Fa hFa_mem F₂ hF₂_mem E_skel hE_mem
        ((hE_le Fa hvFa).2 hu₀₂_Fa) ((hE_le F₂ hvF₂).2 hu₀₂_in) hFa_good
    -- Step 2: Propagate across the 1-skeleton of Q
    let TopQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
    let GoodVQ : (Fin 3 → ℝ) → Prop := fun v => ∀ F ∈ ℱ, v ∈ F.val → GoodF F
    have hF₀_facet := (hℱ F₀).1 hF₀_mem
    obtain ⟨v₀, hv₀F₀, hv₀Exp⟩ := exists_exposed_vertex_in_face hQ F₀ hF₀_facet.1
    have hGoodVQ_all : ∀ v ∈ TopQ.val, IsExposed ℝ Q {v} → GoodVQ v := by
      refine vertices_eq_of_nonempty_edge_closed hQ TopQ GoodVQ
        ⟨v₀, hv₀Exp.subset (Set.mem_singleton v₀), hv₀Exp,
          fun F hF hvF => hLocalFan v₀ hv₀Exp F₀ hF₀_mem hv₀F₀ hF₀_good F hF hvF⟩ ?_
      intro u w E_face hE1 _ huExp hwExp huE hwE huGood F hF hwF
      let E_skel : SkeletonFace Q 1 := ⟨E_face, Or.inr (le_of_eq hE1.2)⟩
      have hE_mem : E_skel ∈ ℰ := (hℰ E_skel).2 ((isEdge_iff Q hQ E_skel).2 hE1)
      obtain ⟨FE, hFE_mem, _, _, _, hEFE, _, _⟩ := hDiamond E_skel hE_mem
      have hFE_good : GoodF FE := huGood FE hFE_mem (hEFE huE)
      exact hLocalFan w hwExp FE hFE_mem (hEFE hwE) hFE_good F hF hwF
    intro F hF
    have hF_facet := (hℱ F).1 hF
    obtain ⟨v, hvF, hvExp⟩ := exists_exposed_vertex_in_face hQ F hF_facet.1
    exact hGoodVQ_all v (hvExp.subset (Set.mem_singleton v)) hvExp F hF hvF
  refine ⟨𝒜, ℰ, ℱ, h𝒜, hℰ, hℱ, hDiamond, hDualConn, ?_⟩
  omega
