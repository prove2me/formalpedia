-- Prove2me | solution 1 for Grunbaum2003.polygon_edge_count_eq_vertex_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:13:03.158703+00:00
-- url     : https://prove2.me/submissions/362083b8-6090-4ff5-ae76-49756074abe1

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_simplicial_facet_subfaces_and_bipartite_double_counting
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open scoped BigOperators
open Classical
open Grunbaum2003

section

lemma exposed_eq_convexHull_filter_2d (s : Finset (Fin 2 → ℝ)) {F : Set (Fin 2 → ℝ)}
    [DecidablePred (· ∈ F)]
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin 2 → ℝ))) F) :
    F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨l, hFl⟩ := hF ⟨x, hx⟩
    have hxP : x ∈ convexHull ℝ (s : Set (Fin 2 → ℝ)) := by
      rw [hFl] at hx; exact hx.1
    have hxl : ∀ z ∈ convexHull ℝ (s : Set (Fin 2 → ℝ)), l z ≤ l x := by
      rw [hFl] at hx; exact hx.2
    rw [Finset.convexHull_eq] at hxP ⊢
    rcases hxP with ⟨w, hw0, hw1, hcm⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hcm
    have hcm' : ∑ z ∈ s, w z • z = x := hcm
    have h_zero : ∀ y ∈ s, y ∉ F → w y = 0 := by
      intro y hy hyF
      by_contra hwy
      have hwy_pos : 0 < w y := lt_of_le_of_ne (hw0 y hy) (Ne.symm hwy)
      have hyP : y ∈ convexHull ℝ (s : Set (Fin 2 → ℝ)) := subset_convexHull ℝ _ hy
      have hlt : l y < l x := by
        refine lt_of_le_of_ne (hxl y hyP) (fun heq => hyF ?_)
        rw [hFl]
        exact ⟨hyP, fun z hz => by linarith [hxl z hz]⟩
      have hsum_lt : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l x := by
        apply Finset.sum_lt_sum
        · intro z hz
          exact mul_le_mul_of_nonneg_left (hxl z (subset_convexHull ℝ _ hz)) (hw0 z hz)
        · exact ⟨y, hy, mul_lt_mul_of_pos_left hlt hwy_pos⟩
      have hsum_eq : ∑ z ∈ s, w z * l z = l x := by
        calc ∑ z ∈ s, w z * l z = ∑ z ∈ s, l (w z • z) := by
              refine Finset.sum_congr rfl (fun z _ => ?_)
              rw [l.map_smul, smul_eq_mul]
          _ = l (∑ z ∈ s, w z • z) := (map_sum l _ _).symm
          _ = l x := by rw [hcm']
      have hsum_rhs : ∑ z ∈ s, w z * l x = l x := by
        rw [← Finset.sum_mul, hw1, one_mul]
      linarith
    have h_sum1 : ∑ y ∈ s.filter (· ∈ F), w y = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.filter_subset _ s) (fun y hy hy' =>
        h_zero y hy (fun h => hy' (Finset.mem_filter.2 ⟨hy, h⟩)))
    refine ⟨w, fun y hy => hw0 y (Finset.mem_of_mem_filter y hy), h_sum1, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id h_sum1]
    change ∑ y ∈ s.filter (· ∈ F), w y • y = x
    rw [← hcm']
    exact Finset.sum_subset (Finset.filter_subset _ s) (fun y hy hy' => by
      rw [h_zero y hy (fun h => hy' (Finset.mem_filter.2 ⟨hy, h⟩)), zero_smul])
  · refine convexHull_min ?_ (hF.convex (convex_convexHull ℝ _))
    intro x hx
    exact (Finset.mem_filter.1 hx).2

lemma isExposed_of_eq_max_on_finset_2d (s : Finset (Fin 2 → ℝ))
    (l : StrongDual ℝ (Fin 2 → ℝ)) (M : ℝ)
    (hle : ∀ y ∈ s, l y ≤ M) (hm : ∃ y₀ ∈ s, l y₀ = M) :
    let P := convexHull ℝ (s : Set (Fin 2 → ℝ))
    let F := convexHull ℝ ((s.filter (fun y => l y = M) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ))
    (∀ x ∈ P, l x ≤ M) ∧
    F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} ∧
    IsExposed ℝ P F := by
  intro P F
  rcases hm with ⟨y₀, hy₀, hy₀M⟩
  have hP_le : ∀ x ∈ P, l x ≤ M := by
    have hsub : (s : Set (Fin 2 → ℝ)) ⊆ {x : Fin 2 → ℝ | l x ≤ M} := fun y hy => hle y hy
    have hconv : Convex ℝ {x : Fin 2 → ℝ | l x ≤ M} :=
      convex_halfSpace_le (l : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_sub_P : F ⊆ P := convexHull_mono (by
    intro y hy
    exact (Finset.mem_filter.1 hy).1)
  have hF_eq_M : ∀ x ∈ F, l x = M := by
    have hsub : ((s.filter (fun y => l y = M) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) ⊆
        {x : Fin 2 → ℝ | l x = M} := fun y hy => (Finset.mem_filter.1 hy).2
    have hconv : Convex ℝ {x : Fin 2 → ℝ | l x = M} :=
      convex_hyperplane (l : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_eq : F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    apply Set.Subset.antisymm
    · intro x hx
      refine ⟨hF_sub_P hx, fun y hy => ?_⟩
      linarith [hP_le y hy, hF_eq_M x hx]
    · intro x hx
      have hExp : IsExposed ℝ P {z ∈ P | ∀ y ∈ P, l y ≤ l z} := fun _ => ⟨l, rfl⟩
      have hfilt := exposed_eq_convexHull_filter_2d s hExp
      rw [hfilt] at hx
      refine convexHull_mono ?_ hx
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      refine Finset.mem_filter.2 ⟨hy'.1, le_antisymm (hle y hy'.1) ?_⟩
      have h1 : l y₀ ≤ l y := hy'.2.2 y₀ (subset_convexHull ℝ _ hy₀)
      linarith
  refine ⟨hP_le, hF_eq, fun _ => ⟨l, hF_eq⟩⟩

lemma exposed_singleton_eq_of_lineMap_mem_2d {P : Set (Fin 2 → ℝ)}
    {w a b : Fin 2 → ℝ} (hw : IsExposed ℝ P {w})
    (ha : a ∈ P) (hb : b ∈ P) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hLine : AffineMap.lineMap a b t = w) :
    a = w ∧ b = w := by
  obtain ⟨l, hl⟩ := hw (Set.singleton_nonempty w)
  have hwMem : w ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := hl ▸ Set.mem_singleton w
  have hla : l a ≤ l w := hwMem.2 a ha
  have hlb : l b ≤ l w := hwMem.2 b hb
  have hLw : (1 - t) * l a + t * l b = l w := by
    have h1 := congrArg l hLine
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have hlaEq : l a = l w := by nlinarith
  have hlbEq : l b = l w := by nlinarith
  have haMem : a ∈ ({w} : Set (Fin 2 → ℝ)) := by
    rw [hl]
    exact ⟨ha, fun y hy => (hwMem.2 y hy).trans_eq hlaEq.symm⟩
  have hbMem : b ∈ ({w} : Set (Fin 2 → ℝ)) := by
    rw [hl]
    exact ⟨hb, fun y hy => (hwMem.2 y hy).trans_eq hlbEq.symm⟩
  exact ⟨Set.mem_singleton_iff.mp haMem, Set.mem_singleton_iff.mp hbMem⟩

lemma dual_apply_fin_two (g : StrongDual ℝ (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    g x = g (Pi.single 0 1) * x 0 + g (Pi.single 1 1) * x 1 := by
  have hx : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem solution (P : Set (Fin 2 → ℝ)) (hP : IsDPolytope P) :
    faceCount P 1 = faceCount P 0 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 2 P hP
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound 2 P
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 2 P
  have hPolyCount := @Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.2.2.1 (Set (Fin 2 → ℝ)) (Fin 2 → ℝ)
  let V_set : Set (Fin 2 → ℝ) := {x : Fin 2 → ℝ | IsExposed ℝ P {x}}
  have hV_fin : V_set.Finite := hHull.1
  let V : Finset (Fin 2 → ℝ) := hV_fin.toFinset
  have hV_coe : (V : Set (Fin 2 → ℝ)) = V_set := hV_fin.coe_toFinset
  have hV_sub_P : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
  have hP_eq_V : P = convexHull ℝ (V : Set (Fin 2 → ℝ)) := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    rw [Set.inter_eq_self_of_subset_right hV_sub_P, ← hV_coe] at h1
    exact h1
  have hCardV : faceCount P 0 = V.card := by
    rw [hVBound.1, Set.ncard_eq_toFinset_card V_set hV_fin]
  have hV_ge3 : 3 ≤ V.card := by
    rw [← hCardV]
    exact hVBound.2 hP
  let E_set : Set (Set (Fin 2 → ℝ)) :=
    {F : Set (Fin 2 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 1}
  have hE_sub : E_set ⊆ (fun s : Finset (Fin 2 → ℝ) => convexHull ℝ (s : Set (Fin 2 → ℝ))) ''
      (V.powerset : Set (Finset (Fin 2 → ℝ))) := by
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
  have hE_fin : E_set.Finite :=
    ((V.powerset.finite_toSet).image _).subset hE_sub
  let ℰ : Finset (Set (Fin 2 → ℝ)) := hE_fin.toFinset
  have hCardE : faceCount P 1 = ℰ.card := by
    unfold faceCount
    exact Set.ncard_eq_toFinset_card E_set hE_fin
  rw [hCardE, hCardV]
  refine hPolyCount ℰ V (fun E v => v ∈ E) ?_ ?_
  · intro E hE
    have hE' : E ∈ E_set := hE_fin.mem_toFinset.1 hE
    obtain ⟨a, b, ha, hb, hab, hEV, _⟩ := (hEdgePair hHull E hE'.2.1).1 ⟨hE'.1, hE'.2.2⟩
    have hfilt : V.filter (fun v => v ∈ E) = {a, b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rw [hV_fin.mem_toFinset, and_comm]
      change x ∈ E ∩ V_set ↔ x = a ∨ x = b
      rw [hEV]
      simp
    rw [hfilt, Finset.card_pair hab]
  · intro v hvV
    have hvExp : IsExposed ℝ P {v} := hV_fin.mem_toFinset.1 hvV
    obtain ⟨l, hvl⟩ := hvExp (Set.singleton_nonempty v)
    have hv_mem : v ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
      rw [← hvl]; exact Set.mem_singleton v
    let a : ℝ := l (Pi.single 0 1)
    let b : ℝ := l (Pi.single 1 1)
    let τ : StrongDual ℝ (Fin 2 → ℝ) :=
      -b • ContinuousLinearMap.proj 0 + a • ContinuousLinearMap.proj 1
    have hl_val : ∀ x : Fin 2 → ℝ, l x = a * x 0 + b * x 1 :=
      fun x => dual_apply_fin_two l x
    have hτ_val : ∀ x : Fin 2 → ℝ, τ x = -b * x 0 + a * x 1 := by
      intro x
      change -b * x 0 + a * x 1 = -b * x 0 + a * x 1
      rfl
    let V' : Finset (Fin 2 → ℝ) := V.erase v
    have hV'_card : 2 ≤ V'.card := by
      rw [Finset.card_erase_of_mem hvV]
      omega
    have hV'_ne : V'.Nonempty := Finset.card_pos.1 (by omega)
    have hl_lt : ∀ w ∈ V', 0 < l v - l w := by
      intro w hw'
      have hwV : w ∈ V := Finset.mem_of_mem_erase hw'
      have hwv : w ≠ v := Finset.ne_of_mem_erase hw'
      have hwP : w ∈ P := hV_sub_P (hV_fin.mem_toFinset.1 hwV)
      have hle : l w ≤ l v := hv_mem.2 w hwP
      have hlt : l w < l v := by
        refine lt_of_le_of_ne hle (fun heq => hwv ?_)
        have hw_in : w ∈ ({v} : Set (Fin 2 → ℝ)) := by
          rw [hvl]
          exact ⟨hwP, fun y hy => by linarith [hv_mem.2 y hy]⟩
        exact Set.mem_singleton_iff.1 hw_in
      linarith
    have hab_pos : 0 < a ^ 2 + b ^ 2 := by
      rcases hV'_ne with ⟨w₀, hw₀⟩
      have hpos := hl_lt w₀ hw₀
      rw [hl_val v, hl_val w₀] at hpos
      by_contra hle
      have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      rw [ha0, hb0] at hpos
      linarith
    let σ : (Fin 2 → ℝ) → ℝ := fun w => (τ w - τ v) / (l v - l w)
    have hσ_mul : ∀ w ∈ V', τ w - τ v = σ w * (l v - l w) := by
      intro w hw'
      dsimp [σ]
      exact (div_mul_cancel₀ _ (ne_of_gt (hl_lt w hw'))).symm
    have h_cramer_eq : ∀ x y : Fin 2 → ℝ, l x = l y → τ x = τ y → x = y := by
      intro x y hlxy hτxy
      rw [hl_val x, hl_val y] at hlxy
      rw [hτ_val x, hτ_val y] at hτxy
      have hx0 : (a ^ 2 + b ^ 2) * (x 0 - y 0) =
          a * (a * x 0 + b * x 1 - (a * y 0 + b * y 1)) -
          b * (-b * x 0 + a * x 1 - (-b * y 0 + a * y 1)) := by ring
      have hx1 : (a ^ 2 + b ^ 2) * (x 1 - y 1) =
          b * (a * x 0 + b * x 1 - (a * y 0 + b * y 1)) +
          a * (-b * x 0 + a * x 1 - (-b * y 0 + a * y 1)) := by ring
      rw [hlxy, sub_self, mul_zero, hτxy, sub_self, mul_zero, sub_zero] at hx0
      rw [hlxy, sub_self, mul_zero, hτxy, sub_self, mul_zero, add_zero] at hx1
      have h0 : x 0 = y 0 := by nlinarith
      have h1 : x 1 = y 1 := by nlinarith
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hσ_inj : ∀ w₁ ∈ V', ∀ w₂ ∈ V', σ w₁ = σ w₂ → w₁ = w₂ := by
      intro w₁ hw₁ w₂ hw₂ hσeq
      have hpos₁ : 0 < l v - l w₁ := hl_lt w₁ hw₁
      have hpos₂ : 0 < l v - l w₂ := hl_lt w₂ hw₂
      have h_le_case : ∀ u₁ ∈ V', ∀ u₂ ∈ V', σ u₁ = σ u₂ → l v - l u₁ ≤ l v - l u₂ → u₁ = u₂ := by
        intro u₁ hu₁ u₂ hu₂ hσu hleu
        have hu₁_pos : 0 < l v - l u₁ := hl_lt u₁ hu₁
        have hu₂_pos : 0 < l v - l u₂ := hl_lt u₂ hu₂
        let t : ℝ := (l v - l u₁) / (l v - l u₂)
        have ht0 : 0 < t := div_pos hu₁_pos hu₂_pos
        have ht1 : t ≤ 1 := (div_le_one hu₂_pos).2 hleu
        let z : Fin 2 → ℝ := AffineMap.lineMap v u₂ t
        have hz_def : z = (1 - t) • v + t • u₂ := AffineMap.lineMap_apply_module v u₂ t
        have hlz : l z = l u₁ := by
          rw [hz_def, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have htmul : t * (l v - l u₂) = l v - l u₁ := div_mul_cancel₀ _ (ne_of_gt hu₂_pos)
          linarith
        have hτz : τ z = τ u₁ := by
          rw [hz_def, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have htmul : t * (l v - l u₂) = l v - l u₁ := div_mul_cancel₀ _ (ne_of_gt hu₂_pos)
          have hτ₁ := hσ_mul u₁ hu₁
          have hτ₂ := hσ_mul u₂ hu₂
          calc (1 - t) * τ v + t * τ u₂
              = τ v + t * (τ u₂ - τ v) := by ring
            _ = τ v + t * (σ u₁ * (l v - l u₂)) := by rw [hτ₂, ← hσu]
            _ = τ v + σ u₁ * (t * (l v - l u₂)) := by ring
            _ = τ v + σ u₁ * (l v - l u₁) := by rw [htmul]
            _ = τ u₁ := by linarith [hτ₁]
        have hzu₁ : z = u₁ := h_cramer_eq z u₁ hlz hτz
        rcases lt_or_eq_of_le ht1 with ht_lt1 | ht_eq1
        · have hu₁Exp : IsExposed ℝ P {u₁} :=
            hV_fin.mem_toFinset.1 (Finset.mem_of_mem_erase hu₁)
          have hvP : v ∈ P := hV_sub_P hvExp
          have hu₂P : u₂ ∈ P := hV_sub_P (hV_fin.mem_toFinset.1 (Finset.mem_of_mem_erase hu₂))
          have hvu₁ := (exposed_singleton_eq_of_lineMap_mem_2d hu₁Exp hvP hu₂P ht0 ht_lt1 hzu₁).1
          exact False.elim ((Finset.ne_of_mem_erase hu₁) hvu₁.symm)
        · dsimp [z] at hzu₁
          rw [ht_eq1, AffineMap.lineMap_apply_one] at hzu₁
          exact hzu₁.symm
      rcases le_total (l v - l w₁) (l v - l w₂) with hle | hle
      · exact h_le_case w₁ hw₁ w₂ hw₂ hσeq hle
      · exact (h_le_case w₂ hw₂ w₁ hw₁ hσeq.symm hle).symm
    obtain ⟨w_max, hw_max, hσ_max⟩ := V'.exists_max_image σ hV'_ne
    obtain ⟨w_min, hw_min, hσ_min⟩ := V'.exists_min_image σ hV'_ne
    have hσ_lt_max : ∀ w ∈ V', w ≠ w_max → σ w < σ w_max := by
      intro w hw hne
      exact lt_of_le_of_ne (hσ_max w hw) (fun heq => hne (hσ_inj w hw w_max hw_max heq))
    have hσ_min_lt : ∀ w ∈ V', w ≠ w_min → σ w_min < σ w := by
      intro w hw hne
      exact lt_of_le_of_ne (hσ_min w hw) (fun heq => hne (hσ_inj w hw w_min hw_min heq.symm))
    have hw_min_ne_max : w_min ≠ w_max := by
      intro heq
      have hsub : V' ⊆ {w_max} := by
        intro w hw
        rw [Finset.mem_singleton]
        by_contra hne
        have h1 := hσ_lt_max w hw hne
        have h2 := hσ_min w hw
        rw [heq] at h2
        linarith
      have hcard_le := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hcard_le
      omega
    let E_plus : Set (Fin 2 → ℝ) := convexHull ℝ ({v, w_max} : Set (Fin 2 → ℝ))
    let E_minus : Set (Fin 2 → ℝ) := convexHull ℝ ({v, w_min} : Set (Fin 2 → ℝ))
    have hE_plus_mem : E_plus ∈ ℰ := by
      rw [hE_fin.mem_toFinset]
      let g_plus : StrongDual ℝ (Fin 2 → ℝ) := σ w_max • l + τ
      have hg_diff : ∀ w ∈ V', g_plus w - g_plus v = (l v - l w) * (σ w - σ w_max) := by
        intro w hw
        have hτw : τ w = σ w * (l v - l w) + τ v := sub_eq_iff_eq_add.1 (hσ_mul w hw)
        change (σ w_max * l w + τ w) - (σ w_max * l v + τ v) = (l v - l w) * (σ w - σ w_max)
        rw [hτw]
        ring
      have hg_le : ∀ w ∈ V, g_plus w ≤ g_plus v := by
        intro w hw
        by_cases hwv : w = v
        · subst hwv; exact le_rfl
        · have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwv, hw⟩
          have hpos := hl_lt w hw'
          have hle := hσ_max w hw'
          have hdiff := hg_diff w hw'
          nlinarith
      have hfilt_plus : V.filter (fun w => g_plus w = g_plus v) = {v, w_max} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hwV, heq⟩
          by_cases hwv : w = v
          · exact Or.inl hwv
          · right
            have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwv, hwV⟩
            by_contra hne
            have hpos := hl_lt w hw'
            have hlt := hσ_lt_max w hw' hne
            have hdiff := hg_diff w hw'
            nlinarith
        · rintro (rfl | hweq)
          · exact ⟨hvV, rfl⟩
          · subst w
            refine ⟨Finset.mem_of_mem_erase hw_max, ?_⟩
            have hdiff := hg_diff w_max hw_max
            rw [sub_self, mul_zero] at hdiff
            exact sub_eq_zero.1 hdiff
      have hexp := isExposed_of_eq_max_on_finset_2d V g_plus (g_plus v) hg_le ⟨v, hvV, rfl⟩
      have hExp_plus : IsExposed ℝ P E_plus := by
        have h1 := hexp.2.2
        rw [← hP_eq_V, hfilt_plus] at h1
        simpa [E_plus] using h1
      have hvw_ne : v ≠ w_max := (Finset.ne_of_mem_erase hw_max).symm
      have hdim1 : Module.finrank ℝ (affineSpan ℝ E_plus).direction = 1 := by
        dsimp [E_plus]
        rw [affineSpan_convexHull, direction_affineSpan, vectorSpan_pair ℝ v w_max]
        exact finrank_span_singleton (vsub_ne_zero.2 hvw_ne)
      exact ⟨⟨v, subset_convexHull ℝ _ (by simp)⟩, hExp_plus, hdim1⟩
    have hE_minus_mem : E_minus ∈ ℰ := by
      rw [hE_fin.mem_toFinset]
      let g_minus : StrongDual ℝ (Fin 2 → ℝ) := -σ w_min • l - τ
      have hg_diff : ∀ w ∈ V', g_minus w - g_minus v = (l v - l w) * (σ w_min - σ w) := by
        intro w hw
        have hτw : τ w = σ w * (l v - l w) + τ v := sub_eq_iff_eq_add.1 (hσ_mul w hw)
        change (-σ w_min * l w - τ w) - (-σ w_min * l v - τ v) = (l v - l w) * (σ w_min - σ w)
        rw [hτw]
        ring
      have hg_le : ∀ w ∈ V, g_minus w ≤ g_minus v := by
        intro w hw
        by_cases hwv : w = v
        · subst hwv; exact le_rfl
        · have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwv, hw⟩
          have hpos := hl_lt w hw'
          have hle := hσ_min w hw'
          have hdiff := hg_diff w hw'
          nlinarith
      have hfilt_minus : V.filter (fun w => g_minus w = g_minus v) = {v, w_min} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hwV, heq⟩
          by_cases hwv : w = v
          · exact Or.inl hwv
          · right
            have hw' : w ∈ V' := Finset.mem_erase.2 ⟨hwv, hwV⟩
            by_contra hne
            have hpos := hl_lt w hw'
            have hlt := hσ_min_lt w hw' hne
            have hdiff := hg_diff w hw'
            nlinarith
        · rintro (rfl | hweq)
          · exact ⟨hvV, rfl⟩
          · subst w
            refine ⟨Finset.mem_of_mem_erase hw_min, ?_⟩
            have hdiff := hg_diff w_min hw_min
            rw [sub_self, mul_zero] at hdiff
            exact sub_eq_zero.1 hdiff
      have hexp := isExposed_of_eq_max_on_finset_2d V g_minus (g_minus v) hg_le ⟨v, hvV, rfl⟩
      have hExp_minus : IsExposed ℝ P E_minus := by
        have h1 := hexp.2.2
        rw [← hP_eq_V, hfilt_minus] at h1
        simpa [E_minus] using h1
      have hvw_ne : v ≠ w_min := (Finset.ne_of_mem_erase hw_min).symm
      have hdim1 : Module.finrank ℝ (affineSpan ℝ E_minus).direction = 1 := by
        dsimp [E_minus]
        rw [affineSpan_convexHull, direction_affineSpan, vectorSpan_pair ℝ v w_min]
        exact finrank_span_singleton (vsub_ne_zero.2 hvw_ne)
      exact ⟨⟨v, subset_convexHull ℝ _ (by simp)⟩, hExp_minus, hdim1⟩
    have hE_ne : E_plus ≠ E_minus := by
      intro heq
      have hE_plus_set : E_plus ∈ E_set := hE_fin.mem_toFinset.1 hE_plus_mem
      have hE_minus_set : E_minus ∈ E_set := hE_fin.mem_toFinset.1 hE_minus_mem
      have hEV_plus : E_plus ∩ V_set = {v, w_max} := by
        obtain ⟨x₁, x₂, hx₁, hx₂, hxne, hEV, hEconv⟩ :=
          (hEdgePair hHull E_plus hE_plus_set.2.1).1 ⟨hE_plus_set.1, hE_plus_set.2.2⟩
        have hv_in : v ∈ E_plus ∩ V_set := ⟨subset_convexHull ℝ _ (by simp), hvExp⟩
        have hw_in : w_max ∈ E_plus ∩ V_set :=
          ⟨subset_convexHull ℝ _ (by simp), hV_fin.mem_toFinset.1 (Finset.mem_of_mem_erase hw_max)⟩
        rw [hEV] at hv_in hw_in ⊢
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv_in hw_in ⊢
        have hvw : v ≠ w_max := (Finset.ne_of_mem_erase hw_max).symm
        rcases hv_in with rfl | rfl <;> rcases hw_in with rfl | rfl
        · exact False.elim (hvw rfl)
        · exact Iff.rfl
        · exact or_comm
        · exact False.elim (hvw rfl)
      have hw_min_in : w_min ∈ E_plus ∩ V_set := by
        rw [heq]
        exact ⟨subset_convexHull ℝ _ (by simp),
          hV_fin.mem_toFinset.1 (Finset.mem_of_mem_erase hw_min)⟩
      rw [hEV_plus, Set.mem_insert_iff, Set.mem_singleton_iff] at hw_min_in
      rcases hw_min_in with h1 | h2
      · exact (Finset.ne_of_mem_erase hw_min) h1
      · exact hw_min_ne_max h2
    have hfilt_E : ℰ.filter (fun E => v ∈ E) = {E_plus, E_minus} := by
      ext E
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun ⟨hE_mem, hvE⟩ => ?_, ?_⟩
      · have hE' : E ∈ E_set := hE_fin.mem_toFinset.1 hE_mem
        obtain ⟨x₁, x₂, hx₁, hx₂, hxne, hEV, hEconv⟩ :=
          (hEdgePair hHull E hE'.2.1).1 ⟨hE'.1, hE'.2.2⟩
        have hv_in : v ∈ E ∩ V_set := ⟨hvE, hvExp⟩
        rw [hEV] at hv_in
        have hex_wE : ∃ w_E ∈ V', E ∩ V_set = {v, w_E} ∧ E = convexHull ℝ ({v, w_E} : Set (Fin 2 → ℝ)) := by
          rcases Set.mem_insert_iff.1 hv_in with rfl | hvx₂
          · refine ⟨x₂, Finset.mem_erase.2 ⟨hxne.symm, hV_fin.mem_toFinset.2 hx₂⟩, hEV, hEconv⟩
          · have hvx₂' : v = x₂ := Set.mem_singleton_iff.1 hvx₂
            subst hvx₂'
            have hpair_comm : ({x₁, v} : Set (Fin 2 → ℝ)) = {v, x₁} := Set.pair_comm x₁ v
            refine ⟨x₁, Finset.mem_erase.2 ⟨hxne, hV_fin.mem_toFinset.2 hx₁⟩, ?_, ?_⟩
            · rwa [hpair_comm] at hEV
            · rwa [hpair_comm] at hEconv
        rcases hex_wE with ⟨w_E, hw_E, hEV_w, hEconv_w⟩
        obtain ⟨g, hEg⟩ := hE'.2.1 hE'.1
        let c : ℝ := g (Pi.single 0 1)
        let d : ℝ := g (Pi.single 1 1)
        have hg_val : ∀ x : Fin 2 → ℝ, g x = c * x 0 + d * x 1 :=
          fun x => dual_apply_fin_two g x
        have hg_id : ∀ w ∈ V', (a ^ 2 + b ^ 2) * (g w - g v) =
            (l v - l w) * (-(a * c + b * d) + (a * d - b * c) * σ w) := by
          intro w hw'
          calc (a ^ 2 + b ^ 2) * (g w - g v)
              = (a ^ 2 + b ^ 2) * (c * w 0 + d * w 1 - (c * v 0 + d * v 1)) := by
                  rw [hg_val w, hg_val v]
            _ = -(a * c + b * d) * (a * v 0 + b * v 1 - (a * w 0 + b * w 1)) +
                (a * d - b * c) * (-b * w 0 + a * w 1 - (-b * v 0 + a * v 1)) := by ring
            _ = -(a * c + b * d) * (l v - l w) + (a * d - b * c) * (τ w - τ v) := by
                rw [← hl_val v, ← hl_val w, ← hτ_val w, ← hτ_val v]
            _ = (l v - l w) * (-(a * c + b * d) + (a * d - b * c) * σ w) := by
                rw [hσ_mul w hw']
                ring
        have hv_Eg : v ∈ {x ∈ P | ∀ y ∈ P, g y ≤ g x} := by
          rw [← hEg]; exact hvE
        have hw_E_Eg : w_E ∈ {x ∈ P | ∀ y ∈ P, g y ≤ g x} := by
          rw [← hEg]
          have hw_in : w_E ∈ E ∩ V_set := by rw [hEV_w]; simp
          exact hw_in.1
        have hgwE_eq : g w_E = g v :=
          le_antisymm (hv_Eg.2 w_E hw_E_Eg.1) (hw_E_Eg.2 v hv_Eg.1)
        have h_wE_zero : -(a * c + b * d) + (a * d - b * c) * σ w_E = 0 := by
          have hid := hg_id w_E hw_E
          rw [hgwE_eq, sub_self, mul_zero] at hid
          have hpos := hl_lt w_E hw_E
          rcases mul_eq_zero.1 hid.symm with h0 | h0
          · linarith
          · exact h0
        have hg_lt_of_ne : ∀ w ∈ V', w ≠ w_E → (a * d - b * c) * (σ w - σ w_E) < 0 := by
          intro w hw' hne
          have hwP : w ∈ P := hV_sub_P (hV_fin.mem_toFinset.1 (Finset.mem_of_mem_erase hw'))
          have hgw_lt : g w < g v := by
            refine lt_of_le_of_ne (hv_Eg.2 w hwP) (fun heq => hne ?_)
            have hwE : w ∈ E := by
              rw [hEg]
              exact ⟨hwP, fun y hy => by linarith [hv_Eg.2 y hy]⟩
            have hw_in : w ∈ E ∩ V_set := ⟨hwE, hV_fin.mem_toFinset.1 (Finset.mem_of_mem_erase hw')⟩
            rw [hEV_w, Set.mem_insert_iff, Set.mem_singleton_iff] at hw_in
            rcases hw_in with h1 | h2
            · exact False.elim ((Finset.ne_of_mem_erase hw') h1)
            · exact h2
          have hid := hg_id w hw'
          have hsub : -(a * c + b * d) + (a * d - b * c) * σ w =
              (a * d - b * c) * (σ w - σ w_E) := by linarith [h_wE_zero]
          rw [hsub] at hid
          have hpos_l := hl_lt w hw'
          have hneg : (l v - l w) * ((a * d - b * c) * (σ w - σ w_E)) < 0 := by
            nlinarith
          nlinarith
        by_cases hmax : w_E = w_max
        · left
          rw [hEconv_w, hmax]
        · right
          have hmin : w_E = w_min := by
            by_contra hmin
            have h1 := hg_lt_of_ne w_max hw_max (Ne.symm hmax)
            have h2 := hg_lt_of_ne w_min hw_min (Ne.symm hmin)
            have h3 := hσ_lt_max w_E hw_E hmax
            have h4 := hσ_min_lt w_E hw_E hmin
            nlinarith
          rw [hEconv_w, hmin]
      · rintro (rfl | rfl)
        · exact ⟨hE_plus_mem, subset_convexHull ℝ _ (by simp)⟩
        · exact ⟨hE_minus_mem, subset_convexHull ℝ _ (by simp)⟩
    rw [hfilt_E, Finset.card_pair hE_ne]

end
