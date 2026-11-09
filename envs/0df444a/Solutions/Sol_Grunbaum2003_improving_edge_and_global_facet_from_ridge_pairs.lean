-- Prove2me | solution 1 for Grunbaum2003.improving_edge_and_global_facet_from_ridge_pairs
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:02:58.974778+00:00
-- url     : https://prove2.me/submissions/9738cd4f-3cd9-4c1d-8869-4928edbb6240

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Order.Atoms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped BigOperators
open Classical

open Grunbaum2003

section

lemma exposed_eq_convexHull_filter {n : ℕ} (s : Finset (Fin n → ℝ)) {F : Set (Fin n → ℝ)}
    [DecidablePred (· ∈ F)]
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F) :
    F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨l, hFl⟩ := hF ⟨x, hx⟩
    have hxP : x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) := by
      rw [hFl] at hx; exact hx.1
    have hxl : ∀ z ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l z ≤ l x := by
      rw [hFl] at hx; exact hx.2
    rw [Finset.convexHull_eq] at hxP ⊢
    rcases hxP with ⟨w, hw0, hw1, hcm⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hcm
    have hcm' : ∑ z ∈ s, w z • z = x := hcm
    have h_zero : ∀ y ∈ s, y ∉ F → w y = 0 := by
      intro y hy hyF
      by_contra hwy
      have hwy_pos : 0 < w y := lt_of_le_of_ne (hw0 y hy) (Ne.symm hwy)
      have hyP : y ∈ convexHull ℝ (s : Set (Fin n → ℝ)) := subset_convexHull ℝ _ hy
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

lemma isExposed_of_eq_max_on_finset {n : ℕ} (s : Finset (Fin n → ℝ))
    (l : StrongDual ℝ (Fin n → ℝ)) (M : ℝ)
    (hle : ∀ y ∈ s, l y ≤ M) (hm : ∃ y₀ ∈ s, l y₀ = M) :
    let P := convexHull ℝ (s : Set (Fin n → ℝ))
    let F := convexHull ℝ ((s.filter (fun y => l y = M) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
    (∀ x ∈ P, l x ≤ M) ∧
    F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} ∧
    IsExposed ℝ P F := by
  intro P F
  rcases hm with ⟨y₀, hy₀, hy₀M⟩
  have hP_le : ∀ x ∈ P, l x ≤ M := by
    have hsub : (s : Set (Fin n → ℝ)) ⊆ {x : Fin n → ℝ | l x ≤ M} := fun y hy => hle y hy
    have hconv : Convex ℝ {x : Fin n → ℝ | l x ≤ M} :=
      convex_halfSpace_le (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_sub_P : F ⊆ P := convexHull_mono (by
    intro y hy
    exact (Finset.mem_filter.1 hy).1)
  have hF_eq_M : ∀ x ∈ F, l x = M := by
    have hsub : ((s.filter (fun y => l y = M) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
        {x : Fin n → ℝ | l x = M} := fun y hy => (Finset.mem_filter.1 hy).2
    have hconv : Convex ℝ {x : Fin n → ℝ | l x = M} :=
      convex_hyperplane (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_eq : F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    apply Set.Subset.antisymm
    · intro x hx
      refine ⟨hF_sub_P hx, fun y hy => ?_⟩
      linarith [hP_le y hy, hF_eq_M x hx]
    · intro x hx
      have hExp : IsExposed ℝ P {z ∈ P | ∀ y ∈ P, l y ≤ l z} := fun _ => ⟨l, rfl⟩
      have hfilt := exposed_eq_convexHull_filter s hExp
      rw [hfilt] at hx
      refine convexHull_mono ?_ hx
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      refine Finset.mem_filter.2 ⟨hy'.1, le_antisymm (hle y hy'.1) ?_⟩
      have h1 : l y₀ ≤ l y := hy'.2.2 y₀ (subset_convexHull ℝ _ hy₀)
      linarith
  refine ⟨hP_le, hF_eq, fun _ => ⟨l, hF_eq⟩⟩

lemma isExposed_trans_of_convexHull {n : ℕ} (s : Finset (Fin n → ℝ))
    {F G : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F)
    (hG : IsExposed ℝ F G) :
    IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) G := by
  intro hGne
  have hGF : G ⊆ F := hG.subset
  have hFne : F.Nonempty := hGne.mono hGF
  have hFs : F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    exposed_eq_convexHull_filter s hF
  have hGs : G = convexHull ℝ (((s.filter (· ∈ F)).filter (· ∈ G) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    have hG' : IsExposed ℝ (convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) G := by
      rwa [← hFs]
    exact exposed_eq_convexHull_filter (s.filter (· ∈ F)) hG'
  have hfilt_eq : (s.filter (· ∈ F)).filter (· ∈ G) = s.filter (· ∈ G) := by
    ext y
    simp only [Finset.mem_filter, and_assoc, and_congr_right_iff]
    intro _
    exact ⟨fun h => h.2, fun h => ⟨hGF h, h⟩⟩
  have hGs' : G = convexHull ℝ ((s.filter (· ∈ G) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    hGs.trans (by rw [hfilt_eq])
  have hsG_ne : (s.filter (· ∈ G)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hGs', hemp, Finset.coe_empty, convexHull_empty] at hGne
    exact Set.not_nonempty_empty hGne
  rcases hsG_ne with ⟨y₀, hy₀⟩
  have hy₀_mem : y₀ ∈ s ∧ y₀ ∈ G := Finset.mem_filter.1 hy₀
  have hy₀F : y₀ ∈ F := hGF hy₀_mem.2
  obtain ⟨l, hFl⟩ := hF hFne
  obtain ⟨m, hGm⟩ := hG hGne
  let M_l : ℝ := l y₀
  let M_m : ℝ := m y₀
  have hl_le : ∀ y ∈ s, l y ≤ M_l := by
    intro y hy
    have hy₀' : y₀ ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ z ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l z ≤ l x} := by
      rw [← hFl]; exact hy₀F
    exact hy₀'.2 y (subset_convexHull ℝ _ hy)
  have hl_lt : ∀ y ∈ s, y ∉ F → l y < M_l := by
    intro y hy hyF
    refine lt_of_le_of_ne (hl_le y hy) (fun heq => hyF ?_)
    rw [hFl]
    refine ⟨subset_convexHull ℝ _ hy, fun z hz => ?_⟩
    have hy₀' : y₀ ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l w ≤ l x} := by
      rw [← hFl]; exact hy₀F
    linarith [hy₀'.2 z hz]
  have hl_eq : ∀ y ∈ s, y ∈ F → l y = M_l := by
    intro y hy hyF
    have hy' : y ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l w ≤ l x} := by
      rw [← hFl]; exact hyF
    exact le_antisymm (hl_le y hy) (hy'.2 y₀ (subset_convexHull ℝ _ hy₀_mem.1))
  have hm_le : ∀ y ∈ s, y ∈ F → m y ≤ M_m := by
    intro y _ hyF
    have hy₀' : y₀ ∈ {x ∈ F | ∀ z ∈ F, m z ≤ m x} := by
      rw [← hGm]; exact hy₀_mem.2
    exact hy₀'.2 y hyF
  have hm_lt : ∀ y ∈ s, y ∈ F → y ∉ G → m y < M_m := by
    intro y hy hyF hyG
    refine lt_of_le_of_ne (hm_le y hy hyF) (fun heq => hyG ?_)
    rw [hGm]
    refine ⟨hyF, fun z hz => ?_⟩
    have hy₀' : y₀ ∈ {x ∈ F | ∀ w ∈ F, m w ≤ m x} := by
      rw [← hGm]; exact hy₀_mem.2
    linarith [hy₀'.2 z hz]
  have hm_eq : ∀ y ∈ s, y ∈ G → m y = M_m := by
    intro y hy hyG
    have hy' : y ∈ {x ∈ F | ∀ w ∈ F, m w ≤ m x} := by
      rw [← hGm]; exact hyG
    exact le_antisymm (hm_le y hy (hGF hyG)) (hy'.2 y₀ hy₀F)
  let term : (Fin n → ℝ) → ℝ := fun z => (1 + (m z - M_m) ^ 2) / (M_l - l z)
  let C : ℝ := 1 + ∑ y ∈ s.filter (· ∉ F), term y
  have hC_ge : 1 ≤ C := by
    dsimp [C]
    suffices h0 : 0 ≤ ∑ y ∈ s.filter (· ∉ F), term y by linarith
    refine Finset.sum_nonneg (fun y hy => ?_)
    have hy' := Finset.mem_filter.1 hy
    have hpos : 0 < M_l - l y := sub_pos.2 (hl_lt y hy'.1 hy'.2)
    dsimp [term]
    positivity
  let h : StrongDual ℝ (Fin n → ℝ) := C • l + m
  have hh_val : ∀ y ∈ s, (y ∈ G → h y = C * M_l + M_m) ∧ (y ∉ G → h y < C * M_l + M_m) := by
    intro y hy
    change (y ∈ G → C * l y + m y = C * M_l + M_m) ∧ (y ∉ G → C * l y + m y < C * M_l + M_m)
    refine ⟨fun hyG => by rw [hl_eq y hy (hGF hyG), hm_eq y hy hyG], fun hyG => ?_⟩
    by_cases hyF : y ∈ F
    · rw [hl_eq y hy hyF]
      linarith [hm_lt y hy hyF hyG]
    · have hy_mem : y ∈ s.filter (· ∉ F) := Finset.mem_filter.2 ⟨hy, hyF⟩
      have hpos : 0 < M_l - l y := sub_pos.2 (hl_lt y hy hyF)
      have hterm_le : term y ≤ ∑ z ∈ s.filter (· ∉ F), term z := by
        refine Finset.single_le_sum (fun z hz => ?_) hy_mem
        have hz' := Finset.mem_filter.1 hz
        have hzpos : 0 < M_l - l z := sub_pos.2 (hl_lt z hz'.1 hz'.2)
        dsimp [term]
        positivity
      have hC_gt : (1 + (m y - M_m) ^ 2) / (M_l - l y) < C := by
        change term y < 1 + ∑ z ∈ s.filter (· ∉ F), term z
        linarith
      have hmul : 1 + (m y - M_m) ^ 2 < C * (M_l - l y) :=
        (div_lt_iff₀ hpos).1 hC_gt
      have hsq : m y - M_m < 1 + (m y - M_m) ^ 2 := by
        nlinarith [(sq_nonneg (m y - M_m - 1 / 2))]
      linarith
  have hh_le : ∀ y ∈ s, h y ≤ C * M_l + M_m := by
    intro y hy
    by_cases hyG : y ∈ G
    · exact le_of_eq ((hh_val y hy).1 hyG)
    · exact le_of_lt ((hh_val y hy).2 hyG)
  have hh_eq_G : s.filter (fun y => h y = C * M_l + M_m) = s.filter (· ∈ G) := by
    ext y
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hy
    exact ⟨fun heq => by_contra (fun hyG => ne_of_lt ((hh_val y hy).2 hyG) heq),
      fun hyG => (hh_val y hy).1 hyG⟩
  have hexp := isExposed_of_eq_max_on_finset s h (C * M_l + M_m) hh_le
    ⟨y₀, hy₀_mem.1, (hh_val y₀ hy₀_mem.1).1 hy₀_mem.2⟩
  rcases hexp with ⟨_, _, hExp⟩
  rw [hh_eq_G, ← hGs'] at hExp
  exact hExp hGne

lemma exists_unique_max_linear_on_finset {n : ℕ} {t : Finset (Fin n → ℝ)} (ht : t.Nonempty) :
    ∃ v ∈ t, ∃ l : StrongDual ℝ (Fin n → ℝ), ∀ y ∈ t, y ≠ v → l y < l v := by
  induction t using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty ht)
  | @insert a s has ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨v', hv', l', hl'⟩ := ih hs
      rcases lt_trichotomy (l' a) (l' v') with hlt | heq | hgt
      · refine ⟨v', Finset.mem_insert_of_mem hv', l', ?_⟩
        intro y hy hyne
        rcases Finset.mem_insert.1 hy with rfl | hys
        · exact hlt
        · exact hl' y hys hyne
      · have hne : a ≠ v' := fun h => has (h ▸ hv')
        have hex_i : ∃ i : Fin n, a i ≠ v' i := Function.ne_iff.1 hne
        rcases hex_i with ⟨i, hi⟩
        let m : StrongDual ℝ (Fin n → ℝ) :=
          if v' i < a i then ContinuousLinearMap.proj i else -ContinuousLinearMap.proj i
        have hm_lt : m v' < m a := by
          dsimp [m]
          split_ifs with hlt_i
          · exact hlt_i
          · simp only [neg_apply, ContinuousLinearMap.proj_apply, neg_lt_neg_iff]
            exact lt_of_le_of_ne (le_of_not_gt hlt_i) hi
        let term : (Fin n → ℝ) → ℝ := fun z => (1 + (m z - m v') ^ 2) / (l' v' - l' z)
        let C : ℝ := 1 + ∑ z ∈ s.filter (· ≠ v'), term z
        let l : StrongDual ℝ (Fin n → ℝ) := C • l' + m
        have hCl : C * l' a = C * l' v' := by rw [heq]
        refine ⟨a, Finset.mem_insert_self a s, l, ?_⟩
        intro y hy hya
        change C * l' y + m y < C * l' a + m a
        rcases Finset.mem_insert.1 hy with rfl | hys
        · exact False.elim (hya rfl)
        · by_cases hyv' : y = v'
          · subst hyv'
            linarith
          · have hy_mem : y ∈ s.filter (· ≠ v') := Finset.mem_filter.2 ⟨hys, hyv'⟩
            have hpos : 0 < l' v' - l' y := sub_pos.2 (hl' y hys hyv')
            have hterm_le : term y ≤ ∑ z ∈ s.filter (· ≠ v'), term z := by
              refine Finset.single_le_sum (fun z hz => ?_) hy_mem
              have hz' := Finset.mem_filter.1 hz
              have hzpos : 0 < l' v' - l' z := sub_pos.2 (hl' z hz'.1 hz'.2)
              dsimp [term]
              positivity
            have hC_gt : (1 + (m y - m v') ^ 2) / (l' v' - l' y) < C := by
              change term y < 1 + ∑ z ∈ s.filter (· ≠ v'), term z
              linarith
            have hmul : 1 + (m y - m v') ^ 2 < C * (l' v' - l' y) :=
              (div_lt_iff₀ hpos).1 hC_gt
            have hsq : m y - m v' < 1 + (m y - m v') ^ 2 := by
              nlinarith [(sq_nonneg (m y - m v' - 1 / 2))]
            linarith
      · refine ⟨a, Finset.mem_insert_self a s, l', ?_⟩
        intro y hy hya
        rcases Finset.mem_insert.1 hy with rfl | hys
        · exact False.elim (hya rfl)
        · by_cases hyv' : y = v'
          · subst hyv'; exact hgt
          · linarith [hl' y hys hyv']
    · rw [Finset.not_nonempty_iff_eq_empty.1 hs]
      refine ⟨a, Finset.mem_singleton_self a, 0, ?_⟩
      intro y hy hya
      exact False.elim (hya (Finset.mem_singleton.1 hy))

lemma exists_exposed_singleton_of_nonempty {n : ℕ} (s : Finset (Fin n → ℝ))
    {F : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F)
    (hFne : F.Nonempty) :
    ∃ v ∈ F, IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) {v} := by
  have hFs : F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    exposed_eq_convexHull_filter s hF
  have ht_ne : (s.filter (· ∈ F)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hFs, hemp, Finset.coe_empty, convexHull_empty] at hFne
    exact Set.not_nonempty_empty hFne
  obtain ⟨v, hv, l, hl⟩ := exists_unique_max_linear_on_finset ht_ne
  have hv_mem : v ∈ s ∧ v ∈ F := Finset.mem_filter.1 hv
  have hle : ∀ y ∈ s.filter (· ∈ F), l y ≤ l v := by
    intro y hy
    by_cases hyv : y = v
    · subst hyv; exact le_rfl
    · exact le_of_lt (hl y hy hyv)
  have hfilt_v : (s.filter (· ∈ F)).filter (fun y => l y = l v) = {v} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun h => by_contra (fun hyv => ne_of_lt (hl y (Finset.mem_filter.2 ⟨h.1.1, h.1.2⟩) hyv) h.2), ?_⟩
    rintro rfl
    exact ⟨⟨hv_mem.1, hv_mem.2⟩, rfl⟩
  have hexp := isExposed_of_eq_max_on_finset (s.filter (· ∈ F)) l (l v) hle ⟨v, hv, rfl⟩
  rcases hexp with ⟨_, _, hExpF⟩
  rw [hfilt_v, Finset.coe_singleton, convexHull_singleton, ← hFs] at hExpF
  exact ⟨v, hv_mem.2, isExposed_trans_of_convexHull s hF hExpF⟩

lemma exists_exposed_singleton_of_isDPolytope {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    {F : Set (Fin n → ℝ)} (hF : IsExposed ℝ P F) (hFne : F.Nonempty) :
    ∃ v ∈ F, IsExposed ℝ P {v} := by
  rcases hP.1 with ⟨V, hVfin, _, hPV⟩
  let s : Finset (Fin n → ℝ) := hVfin.toFinset
  have hsP : P = convexHull ℝ (s : Set (Fin n → ℝ)) := by
    rw [hPV, Set.Finite.coe_toFinset]
  rw [hsP] at hF ⊢
  exact exists_exposed_singleton_of_nonempty s hF hFne

lemma mem_finset_of_isExposed_singleton {n : ℕ} (s : Finset (Fin n → ℝ)) {v : Fin n → ℝ}
    (hv : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) {v}) :
    v ∈ s := by
  have hfilt := exposed_eq_convexHull_filter s hv
  have hv_mem : v ∈ ({v} : Set (Fin n → ℝ)) := Set.mem_singleton v
  rw [hfilt] at hv_mem
  by_contra hvs
  have hemp : s.filter (· ∈ ({v} : Set (Fin n → ℝ))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x hx hxv
    rw [Set.mem_singleton_iff.1 hxv] at hx
    exact hvs hx
  rw [hemp, Finset.coe_empty, convexHull_empty] at hv_mem
  exact hv_mem

lemma vertices_eq_of_nonempty_edge_closed {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (K : PolytopeFace P)
    (hImp : ∀ (a : Fin n → ℝ), IsExposed ℝ P {a} → a ∈ K.val →
      ∀ (l : StrongDual ℝ (Fin n → ℝ)), (∃ x ∈ K.val, l a < l x) →
        ∃ (E : PolytopeFace P) (b : Fin n → ℝ),
          E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 ∧
          E ≤ K ∧ IsExposed ℝ P {b} ∧ a ∈ E.val ∧ b ∈ E.val ∧ l a < l b)
    (Good : (Fin n → ℝ) → Prop)
    (hNe : ∃ v₀ ∈ K.val, IsExposed ℝ P {v₀} ∧ Good v₀)
    (hClosed : ∀ (u w : Fin n → ℝ) (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      E ≤ K → IsExposed ℝ P {u} → IsExposed ℝ P {w} →
      u ∈ E.val → w ∈ E.val → Good u → Good w) :
    ∀ v ∈ K.val, IsExposed ℝ P {v} → Good v := by
  intro w hwK hwExp
  by_contra hwBad
  rcases hP.1 with ⟨V, hVfin, _, hPV⟩
  let s : Finset (Fin n → ℝ) := hVfin.toFinset
  have hsP : P = convexHull ℝ (s : Set (Fin n → ℝ)) := by
    rw [hPV, Set.Finite.coe_toFinset]
  rcases hNe with ⟨v₀, hv₀K, hv₀Exp, hv₀Good⟩
  let A : Finset (Fin n → ℝ) := s.filter (fun v => v ∈ K.val ∧ IsExposed ℝ P {v} ∧ Good v)
  have hv₀s : v₀ ∈ s := by
    apply mem_finset_of_isExposed_singleton s
    rwa [← hsP]
  have hA_ne : A.Nonempty := ⟨v₀, Finset.mem_filter.2 ⟨hv₀s, hv₀K, hv₀Exp, hv₀Good⟩⟩
  obtain ⟨l, hwl⟩ := hwExp (Set.singleton_nonempty w)
  obtain ⟨a, haA, haMax⟩ := A.exists_max_image l hA_ne
  rcases (Finset.mem_filter.1 haA) with ⟨_, haK, haExp, haGood⟩
  have haw_ne : a ≠ w := fun h => hwBad (h ▸ haGood)
  have hw_mem : w ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    rw [← hwl]; exact Set.mem_singleton w
  have haP : a ∈ P := haExp.subset (Set.mem_singleton a)
  have hla_lt : l a < l w := by
    refine lt_of_le_of_ne (hw_mem.2 a haP) (fun heq => haw_ne ?_)
    have ha_in_w : a ∈ ({w} : Set (Fin n → ℝ)) := by
      rw [hwl]
      exact ⟨haP, fun y hy => by linarith [hw_mem.2 y hy]⟩
    exact Set.mem_singleton_iff.1 ha_in_w
  obtain ⟨E, b, hEne, hE1, hEK, hbExp, haE, hbE, hlab⟩ :=
    hImp a haExp haK l ⟨w, hwK, hla_lt⟩
  have hbGood : Good b := hClosed a b E ⟨hEne, hE1⟩ hEK haExp hbExp haE hbE haGood
  have hbK : b ∈ K.val := hEK hbE
  have hbs : b ∈ s := by
    apply mem_finset_of_isExposed_singleton s
    rwa [← hsP]
  have hbA : b ∈ A := Finset.mem_filter.2 ⟨hbs, hbK, hbExp, hbGood⟩
  linarith [haMax b hbA]



def botSkeletonFace {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) : SkeletonFace P k :=
  ⟨⟨∅, isExposed_empty⟩, Or.inl rfl⟩

def atomSkeletonFace {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) (v : Fin n → ℝ)
    (hv : IsExposed ℝ P {v}) : SkeletonFace P k :=
  ⟨⟨{v}, hv⟩, Or.inr (by
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le k)⟩

lemma botSkeletonFace_le {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ} (S : SkeletonFace P k) :
    botSkeletonFace P k ≤ S :=
  Set.empty_subset S.val.val

lemma eq_botSkeletonFace_iff {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ} (S : SkeletonFace P k) :
    S = botSkeletonFace P k ↔ ¬ S.val.val.Nonempty := by
  rw [Set.not_nonempty_iff_eq_empty]
  refine ⟨fun h => by rw [h]; rfl, fun h => ?_⟩
  ext x
  change x ∈ S.val.val ↔ x ∈ (∅ : Set (Fin n → ℝ))
  rw [h]

lemma map_botSkeletonFace {n : ℕ} {P Q : Set (Fin n → ℝ)} {k : ℕ}
    (φ : SkeletonFace P k ≃o SkeletonFace Q k) :
    φ (botSkeletonFace P k) = botSkeletonFace Q k := by
  apply le_antisymm
  · have h := (φ.le_iff_le).2 (botSkeletonFace_le (φ.symm (botSkeletonFace Q k)))
    simpa using h
  · exact botSkeletonFace_le _

lemma nonempty_map_skeletonFace_iff {n : ℕ} {P Q : Set (Fin n → ℝ)} {k : ℕ}
    (φ : SkeletonFace P k ≃o SkeletonFace Q k) (S : SkeletonFace P k) :
    (φ S).val.val.Nonempty ↔ S.val.val.Nonempty := by
  rw [← not_iff_not, ← eq_botSkeletonFace_iff, ← eq_botSkeletonFace_iff, ← map_botSkeletonFace φ]
  exact φ.injective.eq_iff

lemma atomSkeletonFace_le_iff {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ}
    (v : Fin n → ℝ) (hv : IsExposed ℝ P {v}) (S : SkeletonFace P k) :
    atomSkeletonFace P k v hv ≤ S ↔ v ∈ S.val.val := by
  change ({v} : Set (Fin n → ℝ)) ⊆ S.val.val ↔ v ∈ S.val.val
  exact Set.singleton_subset_iff

lemma eq_bot_or_eq_atomSkeletonFace {n : ℕ} {P : Set (Fin n → ℝ)} {k : ℕ}
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

lemma map_atomSkeletonFace_exists {n : ℕ} {P Q : Set (Fin n → ℝ)} (hQ : IsDPolytope Q) {k : ℕ}
    (φ : SkeletonFace P k ≃o SkeletonFace Q k) (v : Fin n → ℝ) (hv : IsExposed ℝ P {v}) :
    ∃ (v' : Fin n → ℝ) (hv' : IsExposed ℝ Q {v'}),
      φ (atomSkeletonFace P k v hv) = atomSkeletonFace Q k v' hv' := by
  have hneP : (atomSkeletonFace P k v hv).val.val.Nonempty := Set.singleton_nonempty v
  have hneQ : (φ (atomSkeletonFace P k v hv)).val.val.Nonempty :=
    (nonempty_map_skeletonFace_iff φ _).2 hneP
  obtain ⟨v', hv'mem, hv'Exp⟩ :=
    exists_exposed_singleton_of_isDPolytope hQ (φ (atomSkeletonFace P k v hv)).val.property hneQ
  refine ⟨v', hv'Exp, ?_⟩
  have hle : atomSkeletonFace Q k v' hv'Exp ≤ φ (atomSkeletonFace P k v hv) :=
    (atomSkeletonFace_le_iff v' hv'Exp _).2 hv'mem
  have hle' : φ.symm (atomSkeletonFace Q k v' hv'Exp) ≤ atomSkeletonFace P k v hv :=
    (φ.symm_apply_le).2 hle
  rcases eq_bot_or_eq_atomSkeletonFace v hv _ hle' with hbot | hatom
  · have hne_atomQ : (atomSkeletonFace Q k v' hv'Exp).val.val.Nonempty := Set.singleton_nonempty v'
    have hne_symm : (φ.symm (atomSkeletonFace Q k v' hv'Exp)).val.val.Nonempty :=
      (nonempty_map_skeletonFace_iff φ.symm _).2 hne_atomQ
    exact False.elim (((eq_botSkeletonFace_iff _).1 hbot) hne_symm)
  · have := congrArg φ hatom
    simpa using this.symm

theorem global_facet_from_edge_closed_propagation_and_ridge_pairs (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d)
    (hLocal : ∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
      ∃ G : PolytopeFace Q,
        G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
        (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)))
    (hGlue : ∀ (u w : Fin (d + 1) → ℝ) (G_u G_w : PolytopeFace Q),
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
        G_u = G_w)
    (hImpP : ∀ (a : Fin (d + 1) → ℝ), IsExposed ℝ P {a} → a ∈ F.val →
      ∀ (l : StrongDual ℝ (Fin (d + 1) → ℝ)), (∃ x ∈ F.val, l a < l x) →
        ∃ (E : PolytopeFace P) (b : Fin (d + 1) → ℝ),
          E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 ∧
          E ≤ F ∧ IsExposed ℝ P {b} ∧ a ∈ E.val ∧ b ∈ E.val ∧ l a < l b)
    (hImpQ : ∀ (G : PolytopeFace Q),
      (G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d) →
      ∀ (a : Fin (d + 1) → ℝ), IsExposed ℝ Q {a} → a ∈ G.val →
        ∀ (l : StrongDual ℝ (Fin (d + 1) → ℝ)), (∃ x ∈ G.val, l a < l x) →
          ∃ (E : PolytopeFace Q) (b : Fin (d + 1) → ℝ),
            E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 ∧
            E ≤ G ∧ IsExposed ℝ Q {b} ∧ a ∈ E.val ∧ b ∈ E.val ∧ l a < l b)
    (hRidges : ∀ (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      E ≤ F →
      ∃ R₁ R₂ : SkeletonFace P (d + 1 - 2),
        R₁ ≠ R₂ ∧ R₁.val ≤ F ∧ R₂.val ≤ F ∧ E ≤ R₁.val ∧ E ≤ R₂.val ∧
        (∀ T : SkeletonFace P (d + 1 - 2), R₁ ≤ T → T = R₁) ∧
        (∀ T : SkeletonFace P (d + 1 - 2), R₂ ≤ T → T = R₂))
    (hMaxDimQ : ∀ (T : SkeletonFace Q (d + 1 - 2)),
      (∀ U : SkeletonFace Q (d + 1 - 2), T ≤ U → U = T) →
      T.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ T.val.val).direction = d - 1) :
    ∃ G : PolytopeFace Q,
      G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
      (∀ S : SkeletonFace P (d + 1 - 2), (φ S).val ≤ G ↔ S.val ≤ F) := by
  obtain ⟨v₀, hv₀F, hv₀Exp⟩ := exists_exposed_singleton_of_isDPolytope hP F.property hF.1
  obtain ⟨G, hGne, hGdim, hGv₀⟩ := hLocal v₀ hv₀Exp hv₀F
  let Good : (Fin (d + 1) → ℝ) → Prop := fun v =>
    ∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)
  have hGood_all : ∀ v ∈ F.val, IsExposed ℝ P {v} → Good v := by
    refine vertices_eq_of_nonempty_edge_closed hP F hImpP Good ⟨v₀, hv₀F, hv₀Exp, hGv₀⟩ ?_
    intro u w E hE1 hEF huExp hwExp huE hwE huGood
    have hwF : w ∈ F.val := hEF hwE
    obtain ⟨G_w, hGw_ne, hGw_dim, hGw_compat⟩ := hLocal w hwExp hwF
    obtain ⟨R₁, R₂, hRne, hR₁F, hR₂F, hER₁, hER₂, hR₁max, hR₂max⟩ := hRidges E hE1 hEF
    have hφR₁_max : ∀ U : SkeletonFace Q (d + 1 - 2), φ R₁ ≤ U → U = φ R₁ := by
      intro U hle
      have hle' : R₁ ≤ φ.symm U := (φ.le_symm_apply).2 hle
      have heq := hR₁max (φ.symm U) hle'
      exact (φ.symm_apply_eq).1 heq
    have hφR₂_max : ∀ U : SkeletonFace Q (d + 1 - 2), φ R₂ ≤ U → U = φ R₂ := by
      intro U hle
      have hle' : R₂ ≤ φ.symm U := (φ.le_symm_apply).2 hle
      have heq := hR₂max (φ.symm U) hle'
      exact (φ.symm_apply_eq).1 heq
    have hGGw : G = G_w := hGlue u w G G_w ⟨hGne, hGdim⟩ ⟨hGw_ne, hGw_dim⟩ huGood hGw_compat
      R₁ R₂ hR₁F hR₂F (hER₁ huE) (hER₁ hwE) (hER₂ huE) (hER₂ hwE)
      (hMaxDimQ (φ R₁) hφR₁_max) (hMaxDimQ (φ R₂) hφR₂_max) hRne
    dsimp [Good]
    rw [hGGw]
    exact hGw_compat
  let GoodQ : (Fin (d + 1) → ℝ) → Prop := fun w' =>
    ∃ (v : Fin (d + 1) → ℝ) (hv : IsExposed ℝ P {v}),
      v ∈ F.val ∧ (φ (atomSkeletonFace P (d + 1 - 2) v hv)).val.val = {w'}
  have hGoodQ_ne : ∃ v₀' ∈ G.val, IsExposed ℝ Q {v₀'} ∧ GoodQ v₀' := by
    obtain ⟨v₀', hv₀'Exp, hv₀'eq⟩ := map_atomSkeletonFace_exists hQ φ v₀ hv₀Exp
    have hv₀_in_atom : v₀ ∈ (atomSkeletonFace P (d + 1 - 2) v₀ hv₀Exp).val.val := Set.mem_singleton v₀
    have hatom_le_F : (atomSkeletonFace P (d + 1 - 2) v₀ hv₀Exp).val ≤ F :=
      Set.singleton_subset_iff.2 hv₀F
    have hφatom_le_G : (φ (atomSkeletonFace P (d + 1 - 2) v₀ hv₀Exp)).val ≤ G :=
      (hGv₀ _ hv₀_in_atom).2 hatom_le_F
    have hv₀'G : v₀' ∈ G.val := by
      rw [hv₀'eq] at hφatom_le_G
      exact hφatom_le_G (Set.mem_singleton v₀')
    refine ⟨v₀', hv₀'G, hv₀'Exp, v₀, hv₀Exp, hv₀F, ?_⟩
    rw [hv₀'eq]; rfl
  have hGoodQ_all : ∀ w' ∈ G.val, IsExposed ℝ Q {w'} → GoodQ w' := by
    refine vertices_eq_of_nonempty_edge_closed hQ G (hImpQ G ⟨hGne, hGdim⟩) GoodQ hGoodQ_ne ?_
    intro u' w' E' hE'1 hE'G hu'Exp hw'Exp hu'E' hw'E' hu'GoodQ
    rcases hu'GoodQ with ⟨u, huExp, huF, hu_eq⟩
    have hE'dim : Module.finrank ℝ (affineSpan ℝ E'.val).direction ≤ d + 1 - 2 := by
      omega
    let E_skel' : SkeletonFace Q (d + 1 - 2) := ⟨E', Or.inr hE'dim⟩
    let S : SkeletonFace P (d + 1 - 2) := φ.symm E_skel'
    have hφS : φ S = E_skel' := φ.apply_symm_apply E_skel'
    have hatom_u_le : φ (atomSkeletonFace P (d + 1 - 2) u huExp) ≤ φ S := by
      rw [hφS]
      change (φ (atomSkeletonFace P (d + 1 - 2) u huExp)).val.val ⊆ E'.val
      rw [hu_eq, Set.singleton_subset_iff]
      exact hu'E'
    have huS : u ∈ S.val.val :=
      (atomSkeletonFace_le_iff u huExp S).1 ((φ.le_iff_le).1 hatom_u_le)
    have hφS_le_G : (φ S).val ≤ G := by
      rw [hφS]; exact hE'G
    have hSF : S.val ≤ F := (hGood_all u huF huExp S huS).1 hφS_le_G
    obtain ⟨w, hwExp, hw_eq⟩ := map_atomSkeletonFace_exists hP φ.symm w' hw'Exp
    have hφw : φ (atomSkeletonFace P (d + 1 - 2) w hwExp) = atomSkeletonFace Q (d + 1 - 2) w' hw'Exp := by
      have := congrArg φ hw_eq
      simpa using this.symm
    have hatom_w_le : φ (atomSkeletonFace P (d + 1 - 2) w hwExp) ≤ φ S := by
      rw [hφw, hφS]
      exact (atomSkeletonFace_le_iff w' hw'Exp E_skel').2 hw'E'
    have hwS : w ∈ S.val.val :=
      (atomSkeletonFace_le_iff w hwExp S).1 ((φ.le_iff_le).1 hatom_w_le)
    have hwF : w ∈ F.val := hSF hwS
    refine ⟨w, hwExp, hwF, ?_⟩
    rw [hφw]; rfl
  refine ⟨G, hGne, hGdim, fun S => ?_⟩
  by_cases hSne : S.val.val.Nonempty
  · obtain ⟨v, hvS, hvExp⟩ := exists_exposed_singleton_of_isDPolytope hP S.val.property hSne
    refine ⟨fun hφSG => ?_, fun hSF => (hGood_all v (hSF hvS) hvExp S hvS).2 hSF⟩
    obtain ⟨v', hv'Exp, hv'eq⟩ := map_atomSkeletonFace_exists hQ φ v hvExp
    have hatom_v_le : atomSkeletonFace P (d + 1 - 2) v hvExp ≤ S :=
      (atomSkeletonFace_le_iff v hvExp S).2 hvS
    have hφatom_le_φS : φ (atomSkeletonFace P (d + 1 - 2) v hvExp) ≤ φ S :=
      (φ.le_iff_le).2 hatom_v_le
    rw [hv'eq] at hφatom_le_φS
    have hv'φS : v' ∈ (φ S).val.val := (atomSkeletonFace_le_iff v' hv'Exp (φ S)).1 hφatom_le_φS
    have hv'G : v' ∈ G.val := hφSG hv'φS
    obtain ⟨u, huExp, huF, hu_eq⟩ := hGoodQ_all v' hv'G hv'Exp
    have hatom_eq : φ (atomSkeletonFace P (d + 1 - 2) u huExp) = φ (atomSkeletonFace P (d + 1 - 2) v hvExp) := by
      ext x
      change x ∈ (φ (atomSkeletonFace P (d + 1 - 2) u huExp)).val.val ↔
        x ∈ (φ (atomSkeletonFace P (d + 1 - 2) v hvExp)).val.val
      rw [hu_eq, hv'eq]
      rfl
    have huv_atom : atomSkeletonFace P (d + 1 - 2) u huExp = atomSkeletonFace P (d + 1 - 2) v hvExp :=
      φ.injective hatom_eq
    have hvu : v = u := by
      have hv_in : v ∈ (atomSkeletonFace P (d + 1 - 2) v hvExp).val.val := Set.mem_singleton v
      rw [← huv_atom] at hv_in
      exact Set.mem_singleton_iff.1 hv_in
    subst hvu
    exact (hGood_all v huF hvExp S hvS).1 hφSG
  · have hSbot : S = botSkeletonFace P (d + 1 - 2) := (eq_botSkeletonFace_iff S).2 hSne
    rw [hSbot, map_botSkeletonFace φ]
    exact ⟨fun _ => Set.empty_subset F.val, fun _ => Set.empty_subset G.val⟩




lemma exists_improving_edge_of_isDPolytope {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsDPolytope P)
    (K : PolytopeFace P) (a : Fin n → ℝ) (haExp : IsExposed ℝ P {a}) (haK : a ∈ K.val)
    (l : StrongDual ℝ (Fin n → ℝ)) (hex : ∃ x ∈ K.val, l a < l x) :
    ∃ (E : PolytopeFace P) (b : Fin n → ℝ),
      E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 ∧
      E ≤ K ∧ IsExposed ℝ P {b} ∧ a ∈ E.val ∧ b ∈ E.val ∧ l a < l b := by
  rcases hP.1 with ⟨V, hVfin, _, hPV⟩
  let s : Finset (Fin n → ℝ) := hVfin.toFinset
  have hsP : P = convexHull ℝ (s : Set (Fin n → ℝ)) := by
    rw [hPV, Set.Finite.coe_toFinset]
  let sK : Finset (Fin n → ℝ) := s.filter (· ∈ K.val)
  have hKExp_s : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) K.val := by
    rw [← hsP]; exact K.property
  have hKs : K.val = convexHull ℝ (sK : Set (Fin n → ℝ)) :=
    exposed_eq_convexHull_filter s hKExp_s
  have has : a ∈ s := by
    apply mem_finset_of_isExposed_singleton s
    rwa [← hsP]
  have hasK : a ∈ sK := Finset.mem_filter.2 ⟨has, haK⟩
  have hex_sK : ∃ z ∈ sK, l a < l z := by
    by_contra hall
    push Not at hall
    rcases hex with ⟨x, hxK, hlax⟩
    have hx_le : l x ≤ l a := by
      rw [hKs] at hxK
      have hsub : (sK : Set (Fin n → ℝ)) ⊆ {w : Fin n → ℝ | l w ≤ l a} := fun z hz => hall z hz
      have hconv : Convex ℝ {w : Fin n → ℝ | l w ≤ l a} :=
        convex_halfSpace_le (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear (l a)
      exact convexHull_min hsub hconv hxK
    linarith
  rcases hex_sK with ⟨z, hz_sK, hlaz⟩
  obtain ⟨h_neg, ha_eq⟩ := haExp (Set.singleton_nonempty a)
  let h : StrongDual ℝ (Fin n → ℝ) := -h_neg
  have hh_pos : ∀ y ∈ s, y ≠ a → 0 < h y - h a := by
    intro y hy hya
    change 0 < -h_neg y - -h_neg a
    have hyP : y ∈ P := by rw [hsP]; exact subset_convexHull ℝ _ hy
    have ha_mem : a ∈ {x ∈ P | ∀ w ∈ P, h_neg w ≤ h_neg x} := by
      rw [← ha_eq]; exact Set.mem_singleton a
    have hle : h_neg y ≤ h_neg a := ha_mem.2 y hyP
    have hlt : h_neg y < h_neg a := by
      refine lt_of_le_of_ne hle (fun heq => hya ?_)
      have hy_in_a : y ∈ ({a} : Set (Fin n → ℝ)) := by
        rw [ha_eq]
        exact ⟨hyP, fun w hw => by linarith [ha_mem.2 w hw]⟩
      exact Set.mem_singleton_iff.1 hy_in_a
    linarith
  let sK' : Finset (Fin n → ℝ) := sK.filter (· ≠ a)
  have hza : z ≠ a := fun h => by subst h; linarith
  have hz' : z ∈ sK' := Finset.mem_filter.2 ⟨hz_sK, hza⟩
  let u : (Fin n → ℝ) → (Fin n → ℝ) := fun y => a + (h y - h a)⁻¹ • (y - a)
  have hu_vec : ∀ y ∈ sK', y - a = (h y - h a) • (u y - a) := by
    intro y hy'
    have hy_s : y ∈ s := (Finset.mem_filter.1 (Finset.mem_filter.1 hy').1).1
    have hya : y ≠ a := (Finset.mem_filter.1 hy').2
    have hpos : 0 < h y - h a := hh_pos y hy_s hya
    dsimp [u]
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  let U : Finset (Fin n → ℝ) := sK'.image u
  have hU_ne : U.Nonempty := ⟨u z, Finset.mem_image_of_mem u hz'⟩
  obtain ⟨w₀, hw₀U, hw₀Max⟩ := U.exists_max_image l hU_ne
  let M_l : ℝ := l w₀
  have hl_uz : l a < l (u z) := by
    have hz_s : z ∈ s := (Finset.mem_filter.1 hz_sK).1
    have hpos : 0 < h z - h a := hh_pos z hz_s hza
    have hvec := congrArg l (hu_vec z hz')
    simp only [map_sub, map_smul, smul_eq_mul] at hvec
    have hprod : 0 < (h z - h a) * (l (u z) - l a) := by linarith
    have hpos2 : 0 < l (u z) - l a := pos_of_mul_pos_right hprod (le_of_lt hpos)
    linarith
  have hl_Ml : l a < M_l := lt_of_lt_of_le hl_uz (hw₀Max (u z) (Finset.mem_image_of_mem u hz'))
  have hexp_U := isExposed_of_eq_max_on_finset U l M_l hw₀Max ⟨w₀, hw₀U, rfl⟩
  let F_U : Set (Fin n → ℝ) := convexHull ℝ ((U.filter (fun w => l w = M_l) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
  have hFU_exp : IsExposed ℝ (convexHull ℝ (U : Set (Fin n → ℝ))) F_U := hexp_U.2.2
  have hw₀_FU : w₀ ∈ F_U := subset_convexHull ℝ _ (Finset.mem_filter.2 ⟨hw₀U, rfl⟩)
  obtain ⟨u_star, hu_star_FU, hu_star_exp⟩ :=
    exists_exposed_singleton_of_nonempty U hFU_exp ⟨w₀, hw₀_FU⟩
  have hu_star_U : u_star ∈ U := mem_finset_of_isExposed_singleton U hu_star_exp
  have hl_ustar_eq : l u_star = M_l := by
    change u_star ∈ convexHull ℝ ((U.filter (fun w => l w = M_l) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) at hu_star_FU
    rw [hexp_U.2.1] at hu_star_FU
    exact le_antisymm (hw₀Max u_star hu_star_U) (hu_star_FU.2 w₀ (subset_convexHull ℝ _ hw₀U))
  have hl_ustar : l a < l u_star := by linarith
  obtain ⟨g, hu_star_eq⟩ := hu_star_exp (Set.singleton_nonempty u_star)
  have hu_star_mem : u_star ∈ {x ∈ convexHull ℝ (U : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (U : Set (Fin n → ℝ)), g w ≤ g x} := by
    rw [← hu_star_eq]; exact Set.mem_singleton u_star
  have hg_le : ∀ w ∈ U, g w ≤ g u_star :=
    fun w hw => hu_star_mem.2 w (subset_convexHull ℝ _ hw)
  have hg_eq_iff : ∀ w ∈ U, g w = g u_star ↔ w = u_star := by
    intro w hw
    refine ⟨fun heq => ?_, fun h => by rw [h]⟩
    have hw_in : w ∈ ({u_star} : Set (Fin n → ℝ)) := by
      rw [hu_star_eq]
      exact ⟨subset_convexHull ℝ _ hw, fun z hz => by linarith [hu_star_mem.2 z hz]⟩
    exact Set.mem_singleton_iff.1 hw_in
  let g_tilde : StrongDual ℝ (Fin n → ℝ) := g - (g u_star - g a) • h
  have hg_tilde_diff : ∀ y ∈ sK', g_tilde y - g_tilde a = (h y - h a) * (g (u y) - g u_star) := by
    intro y hy'
    have hvec := congrArg g (hu_vec y hy')
    simp only [map_sub, map_smul, smul_eq_mul] at hvec
    change (g y - (g u_star - g a) * h y) - (g a - (g u_star - g a) * h a) =
      (h y - h a) * (g (u y) - g u_star)
    linarith
  have hg_tilde_le : ∀ y ∈ sK, g_tilde y ≤ g_tilde a := by
    intro y hy
    by_cases hya : y = a
    · subst hya; exact le_rfl
    · have hy' : y ∈ sK' := Finset.mem_filter.2 ⟨hy, hya⟩
      have hy_s : y ∈ s := (Finset.mem_filter.1 hy).1
      have hpos : 0 < h y - h a := hh_pos y hy_s hya
      have hgle : g (u y) ≤ g u_star := hg_le (u y) (Finset.mem_image_of_mem u hy')
      have hdiff := hg_tilde_diff y hy'
      nlinarith
  have hg_tilde_eq_iff : ∀ y ∈ sK, g_tilde y = g_tilde a ↔ y = a ∨ (y ≠ a ∧ u y = u_star) := by
    intro y hy
    by_cases hya : y = a
    · subst hya; simp
    · have hy' : y ∈ sK' := Finset.mem_filter.2 ⟨hy, hya⟩
      have hy_s : y ∈ s := (Finset.mem_filter.1 hy).1
      have hpos : 0 < h y - h a := hh_pos y hy_s hya
      have hdiff := hg_tilde_diff y hy'
      constructor
      · intro heq
        refine Or.inr ⟨hya, (hg_eq_iff (u y) (Finset.mem_image_of_mem u hy')).1 ?_⟩
        have hmul : (h y - h a) * (g (u y) - g u_star) = 0 := by linarith
        rcases mul_eq_zero.1 hmul with h0 | h0
        · linarith
        · linarith
      · rintro (rfl | ⟨_, huy⟩)
        · exact False.elim (hya rfl)
        · rw [huy] at hdiff
          linarith
  let sE : Finset (Fin n → ℝ) := sK.filter (fun y => g_tilde y = g_tilde a)
  let E_set : Set (Fin n → ℝ) := convexHull ℝ (sE : Set (Fin n → ℝ))
  have hexp_E := isExposed_of_eq_max_on_finset sK g_tilde (g_tilde a) hg_tilde_le ⟨a, hasK, rfl⟩
  have hE_exp_K : IsExposed ℝ K.val E_set := by
    rw [hKs]; exact hexp_E.2.2
  have hE_exp_P : IsExposed ℝ P E_set := by
    rw [hsP]
    exact isExposed_trans_of_convexHull s hKExp_s hE_exp_K
  let E : PolytopeFace P := ⟨E_set, hE_exp_P⟩
  have ha_sE : a ∈ sE := Finset.mem_filter.2 ⟨hasK, rfl⟩
  have haE : a ∈ E.val := subset_convexHull ℝ _ ha_sE
  have hEK : E ≤ K := by
    change E_set ⊆ K.val
    rw [hKs]
    exact convexHull_mono (Finset.filter_subset _ sK)
  let sE' : Finset (Fin n → ℝ) := sK'.filter (fun y => u y = u_star)
  have hsE'_ne : sE'.Nonempty := by
    rcases Finset.mem_image.1 hu_star_U with ⟨y₁, hy₁, hy₁_eq⟩
    exact ⟨y₁, Finset.mem_filter.2 ⟨hy₁, hy₁_eq⟩⟩
  obtain ⟨b, hb_sE', hbMax⟩ := sE'.exists_max_image h hsE'_ne
  rcases Finset.mem_filter.1 hb_sE' with ⟨hb_sK', hub⟩
  rcases Finset.mem_filter.1 hb_sK' with ⟨hb_sK, hba⟩
  have hb_s : b ∈ s := (Finset.mem_filter.1 hb_sK).1
  have hhb_pos : 0 < h b - h a := hh_pos b hb_s hba
  have hb_sE : b ∈ sE := Finset.mem_filter.2 ⟨hb_sK, (hg_tilde_eq_iff b hb_sK).2 (Or.inr ⟨hba, hub⟩)⟩
  have hbE : b ∈ E.val := subset_convexHull ℝ _ hb_sE
  have hba_vec : b - a = (h b - h a) • (u_star - a) := by
    rw [← hub]
    exact hu_vec b hb_sK'
  have hlab : l a < l b := by
    have hvec := congrArg l hba_vec
    simp only [map_sub, map_smul, smul_eq_mul] at hvec
    have hprod : 0 < (h b - h a) * (l u_star - l a) := mul_pos hhb_pos (sub_pos.2 hl_ustar)
    linarith
  have hh_le_sE : ∀ y ∈ sE, h y ≤ h b := by
    intro y hy
    rcases (hg_tilde_eq_iff y (Finset.mem_filter.1 hy).1).1 (Finset.mem_filter.1 hy).2 with rfl | ⟨hya, huy⟩
    · linarith
    · exact hbMax y (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, hya⟩, huy⟩)
  have hh_eq_b : sE.filter (fun y => h y = h b) = {b} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun hy => ?_, fun hy => by subst hy; exact ⟨hb_sE, rfl⟩⟩
    have hy_sE := Finset.mem_filter.1 hy.1
    rcases (hg_tilde_eq_iff y hy_sE.1).1 hy_sE.2 with rfl | ⟨hya, huy⟩
    · linarith
    · have hy_sK' : y ∈ sK' := Finset.mem_filter.2 ⟨hy_sE.1, hya⟩
      have hy_vec : y - a = (h y - h a) • (u_star - a) := by
        rw [← huy]; exact hu_vec y hy_sK'
      have hdiff : y - a = b - a := by
        rw [hy_vec, hba_vec, hy.2]
      exact sub_left_inj.1 hdiff
  have hexp_b := isExposed_of_eq_max_on_finset sE h (h b) hh_le_sE ⟨b, hb_sE, rfl⟩
  have hbExp_E : IsExposed ℝ E.val {b} := by
    have h1 := hexp_b.2.2
    rwa [hh_eq_b, Finset.coe_singleton, convexHull_singleton] at h1
  have hbExp_P : IsExposed ℝ P {b} := by
    rw [hsP]
    have hE_s : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) E.val := by
      rw [← hsP]; exact E.property
    exact isExposed_trans_of_convexHull s hE_s hbExp_E
  have hSpan_eq : affineSpan ℝ E.val = affineSpan ℝ ({a, b} : Set (Fin n → ℝ)) := by
    change affineSpan ℝ (convexHull ℝ (sE : Set (Fin n → ℝ))) = affineSpan ℝ ({a, b} : Set (Fin n → ℝ))
    rw [affineSpan_convexHull]
    apply le_antisymm
    · rw [affineSpan_le]
      intro y hy
      rcases (hg_tilde_eq_iff y (Finset.mem_filter.1 hy).1).1 (Finset.mem_filter.1 hy).2 with rfl | ⟨hya, huy⟩
      · exact subset_affineSpan ℝ _ (by simp)
      · have hy_sK' : y ∈ sK' := Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, hya⟩
        have hy_vec : y - a = (h y - h a) • (u_star - a) := by
          rw [← huy]; exact hu_vec y hy_sK'
        let c : ℝ := (h y - h a) / (h b - h a)
        have hy_line : AffineMap.lineMap a b c = y := by
          rw [AffineMap.lineMap_apply_module]
          have hcb : c • (b - a) = y - a := by
            rw [hba_vec, smul_smul]
            dsimp [c]
            rw [div_mul_cancel₀ _ (ne_of_gt hhb_pos), ← hy_vec]
          calc (1 - c) • a + c • b = a + c • (b - a) := by
                rw [sub_smul, one_smul, smul_sub]
                abel
            _ = a + (y - a) := by rw [hcb]
            _ = y := add_sub_cancel a y
        rw [← hy_line]
        exact AffineMap.lineMap_mem c
          (subset_affineSpan ℝ _ (by simp))
          (subset_affineSpan ℝ _ (by simp))
    · apply affineSpan_mono
      intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hxb
      · exact ha_sE
      · rw [Set.mem_singleton_iff.1 hxb]
        exact hb_sE
  have hE_dim1 : Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 := by
    rw [hSpan_eq, direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (sub_ne_zero.2 (Ne.symm hba))
  exact ⟨E, b, ⟨a, haE⟩, hE_dim1, hEK, hbExp_P, haE, hbE, hlab⟩


theorem solution :
    (∀ {n : ℕ} {P : Set (Fin n → ℝ)}, IsDPolytope P →
      ∀ (K : PolytopeFace P) (a : Fin n → ℝ), IsExposed ℝ P {a} → a ∈ K.val →
        ∀ (l : StrongDual ℝ (Fin n → ℝ)), (∃ x ∈ K.val, l a < l x) →
          ∃ (E : PolytopeFace P) (b : Fin n → ℝ),
            E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 ∧
            E ≤ K ∧ IsExposed ℝ P {b} ∧ a ∈ E.val ∧ b ∈ E.val ∧ l a < l b) ∧
    (∀ (d : ℕ), 3 ≤ d →
      ∀ (P Q : Set (Fin (d + 1) → ℝ)), IsDPolytope P → IsDPolytope Q →
        ∀ (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
          (F : PolytopeFace P),
          (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) →
          (∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
            ∃ G : PolytopeFace Q,
              G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
              (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F))) →
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
              G_u = G_w) →
          (∀ (E : PolytopeFace P),
            (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
            E ≤ F →
            ∃ R₁ R₂ : SkeletonFace P (d + 1 - 2),
              R₁ ≠ R₂ ∧ R₁.val ≤ F ∧ R₂.val ≤ F ∧ E ≤ R₁.val ∧ E ≤ R₂.val ∧
              (∀ T : SkeletonFace P (d + 1 - 2), R₁ ≤ T → T = R₁) ∧
              (∀ T : SkeletonFace P (d + 1 - 2), R₂ ≤ T → T = R₂)) →
          (∀ (T : SkeletonFace Q (d + 1 - 2)),
            (∀ U : SkeletonFace Q (d + 1 - 2), T ≤ U → U = T) →
            T.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ T.val.val).direction = d - 1) →
          ∃ G : PolytopeFace Q,
            G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
            (∀ S : SkeletonFace P (d + 1 - 2), (φ S).val ≤ G ↔ S.val ≤ F)) := by
  refine ⟨fun hP K a haExp haK l hex =>
    exists_improving_edge_of_isDPolytope hP K a haExp haK l hex, ?_⟩
  intro d hd P Q hP hQ φ F hF hLocal hGlue hRidges hMaxDimQ
  exact global_facet_from_edge_closed_propagation_and_ridge_pairs d hd P Q hP hQ φ F hF
    hLocal hGlue
    (fun a haExp haF l hex => exists_improving_edge_of_isDPolytope hP F a haExp haF l hex)
    (fun G _ a haExp haG l hex => exists_improving_edge_of_isDPolytope hQ G a haExp haG l hex)
    hRidges hMaxDimQ

end

