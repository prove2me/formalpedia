-- Prove2me | solution 1 for Grunbaum2003.three_polytope_even_cycle_facet_bipartition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T00:20:08.549327+00:00
-- url     : https://prove2.me/submissions/5e41876f-d8b7-41c9-8423-331aa002b990

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs
import Theorems.Thm_Grunbaum2003_three_polytope_facet_is_induced_nonseparating_cycle
import Theorems.Thm_Grunbaum2003_three_polytope_dual_graph_and_euler_relations

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Grunbaum2003EvenCycleBipartition
open Grunbaum2003

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

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

theorem sum_pair_eq_add {α : Type*} (s : Finset α) (f : α → ZMod 2) (a b : α)
    (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s)
    (hother : ∀ x ∈ s, x ≠ a → x ≠ b → f x = 0) :
    (∑ x ∈ s, f x) = f a + f b := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxb
    · exact ha
    · rw [Finset.mem_singleton.1 hxb]; exact hb
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair hab]
  · intro x hxs hxab
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxab
    exact hother x hxs hxab.1 hxab.2

theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem zmod2_eq_of_add_eq_zero (x y : ZMod 2) (h : x + y = 0) : x = y := by
  calc x = x + 0 := (add_zero x).symm
    _ = x + (y + y) := by rw [zmod2_add_self y]
    _ = (x + y) + y := (add_assoc x y y).symm
    _ = 0 + y := by rw [h]
    _ = y := zero_add y

theorem edge_has_two_atoms (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q)
    (E : SkeletonFace Q 1)
    (hE : ∀ X : SkeletonFace Q 1, E ≤ X → X = E) :
    ∃ A₁ A₂ : SkeletonFace Q 1,
      (¬ (∀ X : SkeletonFace Q 1, A₁ ≤ X) ∧
        ∀ X : SkeletonFace Q 1, X < A₁ → ∀ Y : SkeletonFace Q 1, X ≤ Y) ∧
      (¬ (∀ X : SkeletonFace Q 1, A₂ ≤ X) ∧
        ∀ X : SkeletonFace Q 1, X < A₂ → ∀ Y : SkeletonFace Q 1, X ≤ Y) ∧
      A₁ ≠ A₂ ∧ A₁ ≤ E ∧ A₂ ≤ E ∧
      ∀ A : SkeletonFace Q 1,
        (¬ (∀ X : SkeletonFace Q 1, A ≤ X) ∧
          ∀ X : SkeletonFace Q 1, X < A → ∀ Y : SkeletonFace Q 1, X ≤ Y) →
        A ≤ E → A = A₁ ∨ A = A₂ := by
  have hHull := polytope_face_eq_convexHull_exposed_vertices 3 Q hQ
  obtain ⟨hEne, hE1⟩ := (isEdge_iff Q hQ E).1 hE
  obtain ⟨a, b, haExp, hbExp, hab_ne, hEV, _⟩ :=
    (exposed_edge_pair_and_simplex_faceCount_choose.1 hHull E.val.val E.val.property).1 ⟨hEne, hE1⟩
  have haE : a ∈ E.val.val := by
    have hm : a ∈ E.val.val ∩ {x : Fin 3 → ℝ | IsExposed ℝ Q {x}} := by rw [hEV]; simp
    exact hm.1
  have hbE : b ∈ E.val.val := by
    have hm : b ∈ E.val.val ∩ {x : Fin 3 → ℝ | IsExposed ℝ Q {x}} := by rw [hEV]; simp
    exact hm.1
  let A₁ : SkeletonFace Q 1 := atomSkeletonFace Q 1 a haExp
  let A₂ : SkeletonFace Q 1 := atomSkeletonFace Q 1 b hbExp
  have hA₁_ne_A₂ : A₁ ≠ A₂ := by
    intro hEq
    have ha_in : a ∈ ({b} : Set (Fin 3 → ℝ)) := by
      change a ∈ A₂.val.val
      rw [← hEq]
      exact Set.mem_singleton a
    exact hab_ne (Set.mem_singleton_iff.1 ha_in)
  refine ⟨A₁, A₂,
    (isAtom_iff hQ A₁).2 ⟨a, haExp, rfl⟩,
    (isAtom_iff hQ A₂).2 ⟨b, hbExp, rfl⟩,
    hA₁_ne_A₂,
    (atomSkeletonFace_le_iff a haExp E).2 haE,
    (atomSkeletonFace_le_iff b hbExp E).2 hbE, ?_⟩
  intro A hA_atom hAE
  obtain ⟨v, hvExp, rfl⟩ := (isAtom_iff hQ A).1 hA_atom
  have hv_in : v ∈ E.val.val ∩ {x : Fin 3 → ℝ | IsExposed ℝ Q {x}} :=
    ⟨(atomSkeletonFace_le_iff v hvExp E).1 hAE, hvExp⟩
  rw [hEV] at hv_in
  rcases Set.mem_insert_iff.1 hv_in with rfl | hvb
  · exact Or.inl rfl
  · have hvb' : v = b := Set.mem_singleton_iff.1 hvb
    subst hvb'
    exact Or.inr rfl

end Grunbaum2003EvenCycleBipartition

open Grunbaum2003 Grunbaum2003EvenCycleBipartition in
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
    ∃ inSide : PolytopeFace Q → Prop,
      (∃ G₁ : PolytopeFace Q,
        (G₁.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G₁.val).direction = 2) ∧ inSide G₁) ∧
      (∃ G₀ : PolytopeFace Q,
        (G₀.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G₀.val).direction = 2) ∧ ¬ inSide G₀) ∧
      (∀ (E : SkeletonFace Q 1) (F₁ F₂ : PolytopeFace Q),
        isEdge E → E ∉ C →
        (F₁.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F₁.val).direction = 2) →
        (F₂.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F₂.val).direction = 2) →
        E.val ≤ F₁ → E.val ≤ F₂ →
        (inSide F₁ ↔ inSide F₂)) := by
  intro isBot isAtom isEdge hInduced hTwoReg hConn hNonsep
  let isFacet : PolytopeFace Q → Prop := fun F =>
    F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2
  obtain ⟨𝒜, ℰ, ℱ, h𝒜, hℰ, hℱ, hDiamond, hDualConn, hEuler⟩ :=
    three_polytope_dual_graph_and_euler_relations Q hQ
  -- Define the F₂-linear maps B : (ℱ → ZMod 2) →ₗ[ZMod 2] (ℰ → ZMod 2)
  -- and ∂₁ : (ℰ → ZMod 2) →ₗ[ZMod 2] (𝒜 → ZMod 2)
  let B : (ℱ → ZMod 2) →ₗ[ZMod 2] (ℰ → ZMod 2) :=
    { toFun := fun x E => ∑ F : ℱ, if E.val.val ≤ F.val then x F else 0
      map_add' := fun x y => by
        ext E
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun F _ => ?_)
        split_ifs <;> simp
      map_smul' := fun r x => by
        ext E
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun F _ => ?_)
        split_ifs <;> simp }
  let d1 : (ℰ → ZMod 2) →ₗ[ZMod 2] (𝒜 → ZMod 2) :=
    { toFun := fun y A => ∑ E : ℰ, if A.val ≤ E.val then y E else 0
      map_add' := fun x y => by
        ext A
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun E _ => ?_)
        split_ifs <;> simp
      map_smul' := fun r x => by
        ext A
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun E _ => ?_)
        split_ifs <;> simp }
  -- 1. Show ker B = span {const 1}
  have h_ker_B : ∀ x : ℱ → ZMod 2, x ∈ LinearMap.ker B ↔ ∀ F₁ F₂ : ℱ, x F₁ = x F₂ := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx F₁ F₂
      have hGood : ∀ F ∈ ℱ, ∀ (hF : F ∈ ℱ), x ⟨F, hF⟩ = x F₂ := by
        refine hDualConn (fun F => ∀ hF : F ∈ ℱ, x ⟨F, hF⟩ = x F₂)
          ⟨F₂.val, F₂.property, fun _ => rfl⟩ ?_
        intro G₁ hG₁ G₂ hG₂ E hE hEG₁ hEG₂ hG₁_eq hG₂'
        by_cases hG₁₂ : G₁ = G₂
        · subst hG₁₂; exact hG₁_eq hG₁
        · obtain ⟨H₁, hH₁, H₂, hH₂, hH₁₂_ne, hEH₁, hEH₂, hH_uniq⟩ := hDiamond E hE
          have hBE : B x ⟨E, hE⟩ = 0 := congr_fun hx ⟨E, hE⟩
          change (∑ F : ℱ, if E.val ≤ F.val then x F else 0) = 0 at hBE
          have hsum2 := sum_pair_eq_add Finset.univ (fun F : ℱ => if E.val ≤ F.val then x F else 0)
            ⟨G₁, hG₁⟩ ⟨G₂, hG₂'⟩ (fun heq => hG₁₂ (congrArg Subtype.val heq))
            (Finset.mem_univ _) (Finset.mem_univ _) ?_
          · rw [hsum2, if_pos hEG₁, if_pos hEG₂] at hBE
            have heq := zmod2_eq_of_add_eq_zero _ _ hBE
            exact heq.symm.trans (hG₁_eq hG₁)
          · intro F _ hFG₁ hFG₂
            rw [ite_eq_right_iff]
            intro hEF
            exfalso
            have h1 := hH_uniq G₁ hG₁ hEG₁
            have h2 := hH_uniq G₂ hG₂ hEG₂
            have h3 := hH_uniq F.val F.property hEF
            rcases h1 with rfl | rfl <;> rcases h2 with h2' | h2'
            · exact hG₁₂ h2'.symm
            · subst h2'
              rcases h3 with h3' | h3'
              · exact hFG₁ (Subtype.ext h3')
              · exact hFG₂ (Subtype.ext h3')
            · subst h2'
              rcases h3 with h3' | h3'
              · exact hFG₂ (Subtype.ext h3')
              · exact hFG₁ (Subtype.ext h3')
            · exact hG₁₂ h2'.symm
      exact hGood F₁.val F₁.property F₁.property
    · intro hconst
      ext ⟨E, hE⟩
      obtain ⟨F₁, hF₁, F₂, hF₂, hF₁₂_ne, hEF₁, hEF₂, hF_uniq⟩ := hDiamond E hE
      change (∑ F : ℱ, if E.val ≤ F.val then x F else 0) = 0
      have hsum2 := sum_pair_eq_add Finset.univ (fun F : ℱ => if E.val ≤ F.val then x F else 0)
        ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩ (fun heq => hF₁₂_ne (congrArg Subtype.val heq))
        (Finset.mem_univ _) (Finset.mem_univ _) ?_
      · rw [hsum2, if_pos hEF₁, if_pos hEF₂, hconst ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩]
        exact zmod2_add_self _
      · intro F _ hFF₁ hFF₂
        rw [ite_eq_right_iff]
        intro hEF
        rcases hF_uniq F.val F.property hEF with h1 | h2
        · exact False.elim (hFF₁ (Subtype.ext h1))
        · exact False.elim (hFF₂ (Subtype.ext h2))
  -- Check that ℱ is nonempty
  rcases hTwoReg.1 with ⟨A_c, hAc_atom, hAc_C⟩
  obtain ⟨E_c, E_c2, hEc_edge, _, hEc_C, _, _, hAc_Ec, _, _⟩ := hTwoReg.2 A_c hAc_atom hAc_C
  have hEc_mem : E_c ∈ ℰ := (hℰ E_c).2 hEc_edge
  obtain ⟨F_init, hF_init, _, _, _, _, _, _⟩ := hDiamond E_c hEc_mem
  have h_ker_B_span : LinearMap.ker B = Submodule.span (ZMod 2) {(1 : ℱ → ZMod 2)} := by
    apply le_antisymm
    · intro x hx
      have hconst := (h_ker_B x).1 hx
      rw [Submodule.mem_span_singleton]
      refine ⟨x ⟨F_init, hF_init⟩, ?_⟩
      ext F
      simp [hconst F ⟨F_init, hF_init⟩]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact (h_ker_B 1).2 (fun _ _ => rfl)
  have h_one_ne_zero_F : (1 : ℱ → ZMod 2) ≠ 0 := by
    intro h0
    have h1 := congr_fun h0 ⟨F_init, hF_init⟩
    exact one_ne_zero h1
  have h_finrank_ker_B : Module.finrank (ZMod 2) (LinearMap.ker B) = 1 := by
    rw [h_ker_B_span]
    exact finrank_span_singleton h_one_ne_zero_F
  have h_finrank_range_B : Module.finrank (ZMod 2) (LinearMap.range B) + 1 = ℱ.card := by
    have hrn := LinearMap.finrank_range_add_finrank_ker B
    rw [h_finrank_ker_B, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
    exact hrn
  -- 2. Show range B ≤ ker d1
  have h_range_B_le_ker_d1 : LinearMap.range B ≤ LinearMap.ker d1 := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    ext ⟨A, hA⟩
    have hA_atom : isAtom A := (h𝒜 A).1 hA
    change (∑ E : ℰ, if A ≤ E.val then (∑ F : ℱ, if E.val.val ≤ F.val then x F else 0) else 0) = 0
    have h_swap :
        (∑ E : ℰ, if A ≤ E.val then (∑ F : ℱ, if E.val.val ≤ F.val then x F else 0) else 0) =
        ∑ F : ℱ, ∑ E : ℰ, (if A ≤ E.val ∧ E.val.val ≤ F.val then x F else 0) := by
      calc (∑ E : ℰ, if A ≤ E.val then (∑ F : ℱ, if E.val.val ≤ F.val then x F else 0) else 0)
          = ∑ E : ℰ, ∑ F : ℱ, (if A ≤ E.val ∧ E.val.val ≤ F.val then x F else 0) := by
            refine Finset.sum_congr rfl (fun E _ => ?_)
            split_ifs with hAE
            · refine Finset.sum_congr rfl (fun F _ => ?_)
              simp [hAE]
            · symm
              refine Finset.sum_eq_zero (fun F _ => ?_)
              simp [hAE]
        _ = ∑ F : ℱ, ∑ E : ℰ, (if A ≤ E.val ∧ E.val.val ≤ F.val then x F else 0) :=
            Finset.sum_comm
    rw [h_swap]
    refine Finset.sum_eq_zero (fun F _ => ?_)
    have hF_facet : isFacet F.val := (hℱ F.val).1 F.property
    by_cases hAF : A.val ≤ F.val
    · obtain ⟨_, hF_reg, _, _⟩ := three_polytope_facet_is_induced_nonseparating_cycle Q hQ F.val hF_facet
      obtain ⟨E₁, E₂, hE₁_edge, hE₂_edge, hE₁F, hE₂F, hE₁₂_ne, hAE₁, hAE₂, hE_uniq⟩ :=
        hF_reg.2 A hA_atom hAF
      have hE₁_mem : E₁ ∈ ℰ := (hℰ E₁).2 hE₁_edge
      have hE₂_mem : E₂ ∈ ℰ := (hℰ E₂).2 hE₂_edge
      have hsum2 := sum_pair_eq_add Finset.univ
        (fun E : ℰ => if A ≤ E.val ∧ E.val.val ≤ F.val then x F else 0)
        ⟨E₁, hE₁_mem⟩ ⟨E₂, hE₂_mem⟩
        (fun heq => hE₁₂_ne (congrArg Subtype.val heq))
        (Finset.mem_univ _) (Finset.mem_univ _) ?_
      · rw [hsum2, if_pos ⟨hAE₁, hE₁F⟩, if_pos ⟨hAE₂, hE₂F⟩]
        exact zmod2_add_self (x F)
      · intro E _ hEE₁ hEE₂
        rw [ite_eq_right_iff]
        rintro ⟨hAE, hEF⟩
        rcases hE_uniq E.val ((hℰ E.val).1 E.property) hEF hAE with h1 | h2
        · exact False.elim (hEE₁ (Subtype.ext h1))
        · exact False.elim (hEE₂ (Subtype.ext h2))
    · refine Finset.sum_eq_zero (fun E _ => ?_)
      rw [ite_eq_right_iff]
      rintro ⟨hAE, hEF⟩
      exact False.elim (hAF (le_trans hAE hEF))
  -- 3. Bound finrank (ker d1) via sumA : (𝒜 → ZMod 2) →ₗ[ZMod 2] ZMod 2
  let sumA : (𝒜 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun z => ∑ A : 𝒜, z A
      map_add' := fun z w => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun r z => by
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, ← Finset.mul_sum] }
  have hAc_mem : A_c ∈ 𝒜 := (h𝒜 A_c).2 hAc_atom
  obtain ⟨v_c, hvc_exp, hAc_eq⟩ := (isAtom_iff hQ A_c).1 hAc_atom
  let A₀ : 𝒜 := ⟨A_c, hAc_mem⟩
  let singleA : 𝒜 → (𝒜 → ZMod 2) := fun A B => if B = A then 1 else 0
  let singleE : ℰ → (ℰ → ZMod 2) := fun E E' => if E' = E then 1 else 0
  have h_pair_in_range : ∀ A : 𝒜,
      singleA A + singleA A₀ ∈ LinearMap.range d1 := by
    let TopQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
    let GoodV : (Fin 3 → ℝ) → Prop := fun v =>
      ∀ (hv : IsExposed ℝ Q {v}) (hAv : atomSkeletonFace Q 1 v hv ∈ 𝒜),
        singleA ⟨atomSkeletonFace Q 1 v hv, hAv⟩ + singleA A₀ ∈ LinearMap.range d1
    have hGood_all : ∀ v ∈ TopQ.val, IsExposed ℝ Q {v} → GoodV v := by
      refine vertices_eq_of_nonempty_edge_closed hQ TopQ GoodV
        ⟨v_c, hvc_exp.subset (Set.mem_singleton v_c), hvc_exp, fun hv' hAv' => ?_⟩ ?_
      · have h_eq : (⟨atomSkeletonFace Q 1 v_c hv', hAv'⟩ : 𝒜) = A₀ := Subtype.ext hAc_eq.symm
        rw [h_eq]
        have h_zero : singleA A₀ + singleA A₀ = 0 := by
          ext B
          exact zmod2_add_self _
        rw [h_zero]
        exact Submodule.zero_mem _
      · intro u w E_face hE1 _ huExp hwExp huE hwE huGood hwExp' hAw
        let E_skel : SkeletonFace Q 1 := ⟨E_face, Or.inr (by omega)⟩
        have hE_edge : isEdge E_skel := (isEdge_iff Q hQ E_skel).2 hE1
        have hE_mem : E_skel ∈ ℰ := (hℰ E_skel).2 hE_edge
        let Au := atomSkeletonFace Q 1 u huExp
        let Aw := atomSkeletonFace Q 1 w hwExp'
        have hAu_atom : isAtom Au := (isAtom_iff hQ Au).2 ⟨u, huExp, rfl⟩
        have hAw_atom : isAtom Aw := (isAtom_iff hQ Aw).2 ⟨w, hwExp', rfl⟩
        have hAu_mem : Au ∈ 𝒜 := (h𝒜 Au).2 hAu_atom
        let Au_sub : 𝒜 := ⟨Au, hAu_mem⟩
        let Aw_sub : 𝒜 := ⟨Aw, hAw⟩
        change singleA Aw_sub + singleA A₀ ∈ LinearMap.range d1
        by_cases huw : Au_sub = Aw_sub
        · rw [← huw]
          exact huGood huExp hAu_mem
        · obtain ⟨B₁, B₂, hB₁_atom, hB₂_atom, _, hB₁E, hB₂E, hB_uniq⟩ :=
            edge_has_two_atoms Q hQ E_skel hE_edge
          have hAuE : Au ≤ E_skel := (atomSkeletonFace_le_iff u huExp E_skel).2 huE
          have hAwE : Aw ≤ E_skel := (atomSkeletonFace_le_iff w hwExp' E_skel).2 hwE
          have hd1_E : d1 (singleE ⟨E_skel, hE_mem⟩) =
              singleA Au_sub + singleA Aw_sub := by
            ext A
            change (∑ E' : ℰ, if A.val ≤ E'.val then
                (if E' = ⟨E_skel, hE_mem⟩ then (1 : ZMod 2) else 0) else 0) =
              (if A = Au_sub then 1 else 0) + (if A = Aw_sub then 1 else 0)
            rw [Finset.sum_eq_single ⟨E_skel, hE_mem⟩]
            · simp only [ ↓reduceIte]
              by_cases hAAu : A = Au_sub
              · subst hAAu
                rw [if_pos hAuE, if_pos rfl, if_neg huw, add_zero]
              · by_cases hAAw : A = Aw_sub
                · subst hAAw
                  rw [if_pos hAwE, if_neg hAAu, if_pos rfl, zero_add]
                · rw [if_neg hAAu, if_neg hAAw, add_zero, ite_eq_right_iff]
                  intro hAE
                  exfalso
                  have h1 := hB_uniq Au hAu_atom hAuE
                  have h2 := hB_uniq Aw hAw_atom hAwE
                  have h3 := hB_uniq A.val ((h𝒜 A.val).1 A.property) hAE
                  rcases h1 with rfl | rfl <;> rcases h2 with h2' | h2'
                  · exact huw (Subtype.ext h2'.symm)
                  · subst h2'
                    rcases h3 with h3' | h3'
                    · exact hAAu (Subtype.ext h3')
                    · exact hAAw (Subtype.ext h3')
                  · subst h2'
                    rcases h3 with h3' | h3'
                    · exact hAAw (Subtype.ext h3')
                    · exact hAAu (Subtype.ext h3')
                  · exact huw (Subtype.ext h2'.symm)
            · intro E' _ hne
              rw [if_neg hne, ite_self]
            · intro habs; exact False.elim (habs (Finset.mem_univ _))
          have h_edge_mem : singleA Au_sub + singleA Aw_sub ∈
              LinearMap.range d1 := ⟨singleE ⟨E_skel, hE_mem⟩, hd1_E⟩
          have h_sum_mem := Submodule.add_mem (LinearMap.range d1) h_edge_mem (huGood huExp hAu_mem)
          have h_cancel :
              (singleA Au_sub + singleA Aw_sub) + (singleA Au_sub + singleA A₀) =
              singleA Aw_sub + singleA A₀ := by
            ext A
            simp only [Pi.add_apply]
            calc (singleA Au_sub A + singleA Aw_sub A) + (singleA Au_sub A + singleA A₀ A)
                = (singleA Au_sub A + singleA Au_sub A) + (singleA Aw_sub A + singleA A₀ A) := by ring
              _ = 0 + (singleA Aw_sub A + singleA A₀ A) := by rw [zmod2_add_self]
              _ = singleA Aw_sub A + singleA A₀ A := zero_add _
          rwa [h_cancel] at h_sum_mem
    intro A
    obtain ⟨v, hvExp, hA_eq⟩ := (isAtom_iff hQ A.val).1 ((h𝒜 A.val).1 A.property)
    have hAv_mem : atomSkeletonFace Q 1 v hvExp ∈ 𝒜 := hA_eq ▸ A.property
    have hres := hGood_all v (hvExp.subset (Set.mem_singleton v)) hvExp hvExp hAv_mem
    have h_sub_eq : (⟨atomSkeletonFace Q 1 v hvExp, hAv_mem⟩ : 𝒜) = A := Subtype.ext hA_eq.symm
    rwa [h_sub_eq] at hres
  have h_ker_sumA_le_range_d1 : LinearMap.ker sumA ≤ LinearMap.range d1 := by
    intro z hz
    have hz0 : (∑ A : 𝒜, z A) = 0 := LinearMap.mem_ker.1 hz
    have h_mem : (∑ A : 𝒜, z A • (singleA A + singleA A₀)) ∈
        LinearMap.range d1 :=
      Submodule.sum_mem (LinearMap.range d1) (fun A _ => Submodule.smul_mem _ _ (h_pair_in_range A))
    have h_eq : (∑ A : 𝒜, z A • (singleA A + singleA A₀)) = z := by
      ext B
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, ← Finset.sum_mul]
      have h1 : (∑ A : 𝒜, z A * singleA A B) = z B := by
        rw [Finset.sum_eq_single B]
        · dsimp [singleA]; rw [if_pos rfl, mul_one]
        · intro A _ hAB
          dsimp [singleA]
          rw [if_neg hAB.symm, mul_zero]
        · intro habs; exact False.elim (habs (Finset.mem_univ B))
      rw [h1, hz0, zero_mul, add_zero]
    rwa [h_eq] at h_mem
  have h_finrank_range_d1_ge : 𝒜.card ≤ Module.finrank (ZMod 2) (LinearMap.range d1) + 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker sumA
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
    have h_le1 : Module.finrank (ZMod 2) (LinearMap.range sumA) ≤ 1 := by
      have h_le := Submodule.finrank_le (LinearMap.range sumA)
      rwa [Module.finrank_self] at h_le
    have h_le2 : Module.finrank (ZMod 2) (LinearMap.ker sumA) ≤
        Module.finrank (ZMod 2) (LinearMap.range d1) :=
      Submodule.finrank_mono h_ker_sumA_le_range_d1
    omega
  have h_finrank_ker_d1_le : Module.finrank (ZMod 2) (LinearMap.ker d1) ≤
      Module.finrank (ZMod 2) (LinearMap.range B) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker d1
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
    omega
  have h_range_B_eq_ker_d1 : LinearMap.range B = LinearMap.ker d1 :=
    Submodule.eq_of_le_of_finrank_le h_range_B_le_ker_d1 h_finrank_ker_d1_le
  -- 4. Indicator vector 1_C ∈ ker d1, hence 1_C = B x for some x : ℱ → ZMod 2
  let y_C : ℰ → ZMod 2 := fun E => if E.val ∈ C then 1 else 0
  have hy_C_ker : y_C ∈ LinearMap.ker d1 := by
    rw [LinearMap.mem_ker]
    ext ⟨A, hA⟩
    have hA_atom : isAtom A := (h𝒜 A).1 hA
    change (∑ E : ℰ, if A ≤ E.val then (if E.val ∈ C then (1 : ZMod 2) else 0) else 0) = 0
    by_cases hAC : A ∈ C
    · obtain ⟨E₁, E₂, hE₁_edge, hE₂_edge, hE₁C, hE₂C, hE₁₂_ne, hAE₁, hAE₂, hE_uniq⟩ :=
        hTwoReg.2 A hA_atom hAC
      have hE₁_mem : E₁ ∈ ℰ := (hℰ E₁).2 hE₁_edge
      have hE₂_mem : E₂ ∈ ℰ := (hℰ E₂).2 hE₂_edge
      have hsum2 := sum_pair_eq_add Finset.univ
        (fun E : ℰ => if A ≤ E.val then (if E.val ∈ C then (1 : ZMod 2) else 0) else 0)
        ⟨E₁, hE₁_mem⟩ ⟨E₂, hE₂_mem⟩
        (fun heq => hE₁₂_ne (congrArg Subtype.val heq))
        (Finset.mem_univ _) (Finset.mem_univ _) ?_
      · rw [hsum2, if_pos hAE₁, if_pos hE₁C, if_pos hAE₂, if_pos hE₂C]
        exact zmod2_add_self 1
      · intro E _ hEE₁ hEE₂
        split_ifs with hAE hEC
        · rcases hE_uniq E.val ((hℰ E.val).1 E.property) hEC hAE with h1 | h2
          · exact False.elim (hEE₁ (Subtype.ext h1))
          · exact False.elim (hEE₂ (Subtype.ext h2))
        · rfl
        · rfl
    · refine Finset.sum_eq_zero (fun E _ => ?_)
      split_ifs with hAE hEC
      · exfalso
        exact hAC ((hInduced E.val).1 hEC A hA_atom hAE)
      · rfl
      · rfl
  rw [← h_range_B_eq_ker_d1] at hy_C_ker
  rcases hy_C_ker with ⟨x, hx⟩
  -- 5. Define inSide F := ∃ hF : F ∈ ℱ, x ⟨F, hF⟩ = 1
  let inSide : PolytopeFace Q → Prop := fun F => ∃ hF : F ∈ ℱ, x ⟨F, hF⟩ = 1
  -- Show E_c ∈ C has y_C ⟨E_c, hEc_mem⟩ = 1, so x is not constant (hence takes both 0 and 1 on ℱ)
  have hy_Ec : B x ⟨E_c, hEc_mem⟩ = 1 := by
    rw [hx]
    dsimp [y_C]
    rw [if_pos hEc_C]
  obtain ⟨F_c1, hFc1, F_c2, hFc2, hFc12_ne, hEc_Fc1, hEc_Fc2, hFc_uniq⟩ := hDiamond E_c hEc_mem
  have hsum_Ec : B x ⟨E_c, hEc_mem⟩ = x ⟨F_c1, hFc1⟩ + x ⟨F_c2, hFc2⟩ := by
    change (∑ F : ℱ, if E_c.val ≤ F.val then x F else 0) = x ⟨F_c1, hFc1⟩ + x ⟨F_c2, hFc2⟩
    have hsum2 := sum_pair_eq_add Finset.univ
      (fun F : ℱ => if E_c.val ≤ F.val then x F else 0)
      ⟨F_c1, hFc1⟩ ⟨F_c2, hFc2⟩
      (fun heq => hFc12_ne (congrArg Subtype.val heq))
      (Finset.mem_univ _) (Finset.mem_univ _) ?_
    · rw [hsum2, if_pos hEc_Fc1, if_pos hEc_Fc2]
    · intro F _ hFF₁ hFF₂
      rw [ite_eq_right_iff]
      intro hEF
      rcases hFc_uniq F.val F.property hEF with h1 | h2
      · exact False.elim (hFF₁ (Subtype.ext h1))
      · exact False.elim (hFF₂ (Subtype.ext h2))
  rw [hsum_Ec] at hy_Ec
  have hx_diff : x ⟨F_c1, hFc1⟩ ≠ x ⟨F_c2, hFc2⟩ := by
    intro heq
    rw [heq, zmod2_add_self] at hy_Ec
    exact zero_ne_one hy_Ec
  have hex_sides :
      (∃ G₁ : PolytopeFace Q, isFacet G₁ ∧ inSide G₁) ∧
      (∃ G₀ : PolytopeFace Q, isFacet G₀ ∧ ¬ inSide G₀) := by
    by_cases h1 : x ⟨F_c1, hFc1⟩ = 1
    · refine ⟨⟨F_c1, (hℱ F_c1).1 hFc1, hFc1, h1⟩, ⟨F_c2, (hℱ F_c2).1 hFc2, ?_⟩⟩
      rintro ⟨_, h2⟩
      exact hx_diff (h1.trans h2.symm)
    · have h2 : x ⟨F_c2, hFc2⟩ = 1 := by
        have h1_val : x ⟨F_c1, hFc1⟩ = 0 := by
          rcases zmod2_eq_zero_or_one (x ⟨F_c1, hFc1⟩) with h0 | h1'
          · exact h0
          · exact False.elim (h1 h1')
        rw [h1_val, zero_add] at hy_Ec
        exact hy_Ec
      refine ⟨⟨F_c2, (hℱ F_c2).1 hFc2, hFc2, h2⟩, ⟨F_c1, (hℱ F_c1).1 hFc1, ?_⟩⟩
      rintro ⟨_, h1'⟩
      exact h1 h1'
  refine ⟨inSide, hex_sides.1, hex_sides.2, ?_⟩
  intro E F₁ F₂ hE_edge hE_out hF₁_facet hF₂_facet hEF₁ hEF₂
  have hE_mem : E ∈ ℰ := (hℰ E).2 hE_edge
  have hF₁_mem : F₁ ∈ ℱ := (hℱ F₁).2 hF₁_facet
  have hF₂_mem : F₂ ∈ ℱ := (hℱ F₂).2 hF₂_facet
  by_cases hF₁₂ : F₁ = F₂
  · subst hF₁₂; exact Iff.rfl
  · obtain ⟨H₁, hH₁, H₂, hH₂, _, _, _, hH_uniq⟩ := hDiamond E hE_mem
    have hyE : B x ⟨E, hE_mem⟩ = 0 := by
      rw [hx]
      dsimp [y_C]
      rw [if_neg hE_out]
    change (∑ F : ℱ, if E.val ≤ F.val then x F else 0) = 0 at hyE
    have hsum2 := sum_pair_eq_add Finset.univ (fun F : ℱ => if E.val ≤ F.val then x F else 0)
      ⟨F₁, hF₁_mem⟩ ⟨F₂, hF₂_mem⟩ (fun heq => hF₁₂ (congrArg Subtype.val heq))
      (Finset.mem_univ _) (Finset.mem_univ _) ?_
    · rw [hsum2, if_pos hEF₁, if_pos hEF₂] at hyE
      have hx_eq := zmod2_eq_of_add_eq_zero _ _ hyE
      dsimp [inSide]
      exact ⟨fun ⟨_, h1⟩ => ⟨hF₂_mem, hx_eq.symm.trans h1⟩,
        fun ⟨_, h2⟩ => ⟨hF₁_mem, hx_eq.trans h2⟩⟩
    · intro F _ hFF₁ hFF₂
      rw [ite_eq_right_iff]
      intro hEF
      exfalso
      have h1 := hH_uniq F₁ hF₁_mem hEF₁
      have h2 := hH_uniq F₂ hF₂_mem hEF₂
      have h3 := hH_uniq F.val F.property hEF
      rcases h1 with rfl | rfl <;> rcases h2 with h2' | h2'
      · exact hF₁₂ h2'.symm
      · subst h2'
        rcases h3 with h3' | h3'
        · exact hFF₁ (Subtype.ext h3')
        · exact hFF₂ (Subtype.ext h3')
      · subst h2'
        rcases h3 with h3' | h3'
        · exact hFF₂ (Subtype.ext h3')
        · exact hFF₁ (Subtype.ext h3')
      · exact hF₁₂ h2'.symm
