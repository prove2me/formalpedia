-- Prove2me | solution 1 for NisanRonen.Rounding.boundedLoadDP_report_certificates_for_remaining_oversubscribed_instances
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T08:03:27.284942+00:00
-- url     : https://prove2.me/submissions/1020db94-6533-41dc-9fb1-b8ba575e239a

import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_exact
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_respects_fixed_priority
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound
import Theorems.Thm_NisanRonen_Rounding_threshold_implication_controls_rounded_bundle_load
import Theorems.Thm_NisanRonen_Rounding_report_subset_optimum_le_singletons
import Theorems.Thm_NisanRonen_Rounding_fixed_priority_stability_of_large_single_report_gap
import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

open NisanRonen.Rounding
open scoped BigOperators

set_option autoImplicit false

private theorem choose_bounded_sum {α : Type} [DecidableEq α] (s : Finset α)
    (L U : α → ℤ) (h : ∀ j ∈ s, L j ≤ U j) (m : ℤ)
    (hL : (∑ j ∈ s, L j) ≤ m) (hU : m ≤ ∑ j ∈ s, U j) :
    ∃ D : α → ℤ, (∀ j ∈ s, L j ≤ D j ∧ D j ≤ U j) ∧ (∑ j ∈ s, D j) = m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    refine ⟨L, by simp, ?_⟩
    simp at hL hU
    simpa using le_antisymm hL hU
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hL hU
    let q := max (L a) (m - ∑ j ∈ s, U j)
    have hqa : L a ≤ q := le_max_left _ _
    have hqu : q ≤ U a := max_le (h a (Finset.mem_insert_self _ _)) (by omega)
    have hremL : (∑ j ∈ s, L j) ≤ m - q := by
      have hsum := Finset.sum_le_sum (f := L) (g := U)
        (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hq : q ≤ m - ∑ j ∈ s, L j := max_le (by omega) (by omega)
      omega
    have hremU : m - q ≤ ∑ j ∈ s, U j := by
      have hq : m - ∑ j ∈ s, U j ≤ q := le_max_right _ _
      omega
    obtain ⟨D, hd, hds⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      (m-q) hremL hremU
    let D' := Function.update D a q
    refine ⟨D', ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa [D'] using And.intro hqa hqu
      · have hjne : j ≠ a := fun e => ha (e ▸ hj)
        simpa [D', Function.update_of_ne hjne] using hd j hj
    · have he : (∑ j ∈ s, D' j) = ∑ j ∈ s, D j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjne : j ≠ a := fun e => ha (e ▸ hj)
        simp [D', Function.update_of_ne hjne]
      rw [Finset.sum_insert ha, he, hds]
      simp [D']

private theorem time_ge {δ u : ℝ} (hδ : 0 < δ) : u ≤ roundUp δ u := by
  have hm := mul_le_mul_of_nonneg_left (Int.le_ceil (u / δ)) hδ.le
  rw [mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem time_mono {δ : ℝ} (hδ : 0 < δ) {u v : ℝ} (h : u ≤ v) :
    roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)) hδ.le

private theorem time_grid {δ : ℝ} (hδ : 0 < δ) (z : ℤ) :
    roundUp δ (δ * (z : ℝ)) = δ * (z : ℝ) := by
  simp [roundUp, mul_div_cancel_left₀ _ hδ.ne']

private theorem cap_row {k : ℕ} {a b δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin k)) (row : Fin k → ℝ) (hrow : ∀ j, a ≤ row j ∧ row j ≤ b)
    (m : ℤ) (hfloor : (∑ _j ∈ S, roundUp δ a) ≤ δ * (m : ℝ)) :
    ∃ newRow : Fin k → ℝ, (∀ j, a ≤ newRow j ∧ newRow j ≤ b) ∧
      (∀ j ∉ S, newRow j = row j) ∧
      (∀ j, roundUp δ (newRow j) ≤ roundUp δ (row j)) ∧
      (∑ j ∈ S, roundUp δ (newRow j)) = min (∑ j ∈ S, roundUp δ (row j)) (δ * (m : ℝ)) := by
  classical
  let L : ℤ := ⌈a / δ⌉
  let U (j : Fin k) : ℤ := ⌈row j / δ⌉
  let z := min (∑ j ∈ S, U j) m
  have hLU (j : Fin k) : L ≤ U j :=
    Int.ceil_mono (div_le_div_of_nonneg_right (hrow j).1 hδ.le)
  have hLf : (∑ _j ∈ S, L) ≤ m := by
    have hm : δ * (↑(∑ _j ∈ S, L) : ℝ) ≤ δ * (m : ℝ) := by
      simpa only [Int.cast_sum, Finset.mul_sum, L, roundUp] using hfloor
    exact_mod_cast (le_of_mul_le_mul_left hm hδ)
  obtain ⟨D, hd, hsum⟩ := choose_bounded_sum S (fun _ => L) U
    (fun j _ => hLU j) z
    (le_min (Finset.sum_le_sum (fun j _ => hLU j)) hLf) (min_le_left _ _)
  let newRow (j : Fin k) := if j ∈ S then min (row j) (δ * (D j : ℝ)) else row j
  have hround (j : Fin k) (hj : j ∈ S) : roundUp δ (newRow j) = δ * (D j : ℝ) := by
    have hD : δ * (D j : ℝ) ≤ roundUp δ (row j) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hd j hj).2) hδ.le
    change roundUp δ (if j ∈ S then min (row j) (δ * (D j : ℝ)) else row j) = _
    rw [if_pos hj]
    by_cases hh : row j ≤ δ * (D j : ℝ)
    · rw [min_eq_left hh]
      exact le_antisymm (by simpa [time_grid hδ] using time_mono hδ hh) hD
    · rw [min_eq_right (le_of_not_ge hh), time_grid hδ]
  refine ⟨newRow, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · have hmin : a ≤ δ * (D j : ℝ) := (time_ge hδ).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (hd j hj).1) hδ.le)
      exact ⟨by simpa only [newRow, if_pos hj] using le_min (hrow j).1 hmin,
        by simpa only [newRow, if_pos hj] using (min_le_left _ _).trans (hrow j).2⟩
    · simpa [newRow, hj] using hrow j
  · intro j hj; simp [newRow, hj]
  · intro j
    apply time_mono hδ
    by_cases hj : j ∈ S <;> simp [newRow, hj]
  · have he : (∑ j ∈ S, roundUp δ (newRow j)) = δ * (z : ℝ) := by
      calc
        (∑ j ∈ S, roundUp δ (newRow j)) = ∑ j ∈ S, δ * (D j : ℝ) :=
          Finset.sum_congr rfl hround
        _ = δ * (z : ℝ) := by rw [← Finset.mul_sum, ← Int.cast_sum, hsum]
    rw [he]
    have hU : (∑ j ∈ S, roundUp δ (row j)) = δ * (↑(∑ j ∈ S, U j) : ℝ) := by
      simp only [Int.cast_sum, Finset.mul_sum, U, roundUp]
    rw [hU]
    rcases le_total (∑ j ∈ S, U j) m with h | h
    · have hc : δ * (↑(∑ j ∈ S, U j) : ℝ) ≤ δ * (m : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hδ.le
      simp only [z, min_eq_left h, min_eq_left hc]
    · have hc : δ * (m : ℝ) ≤ δ * (↑(∑ j ∈ S, U j) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hδ.le
      simp only [z, min_eq_right h, min_eq_right hc]

private noncomputable def rowLoad {n k : ℕ} (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (l : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)

private noncomputable def span {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) : ℝ :=
  roundedMakespan δ x (corrStar x d)

private theorem span_eq {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) :
    span δ x d = Finset.univ.sup' Finset.univ_nonempty (rowLoad δ x d) := by
  unfold span roundedMakespan makespan
  congr 1
  funext l
  unfold rowLoad load
  apply Finset.sum_congr rfl
  intro j hj
  simp [corrStar, (Finset.mem_filter.1 hj).2]

private theorem fixed_priority_cap {n k : ℕ} [NeZero n] {a b δ : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ d : Fin n → Fin k → ℝ, (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
      ∀ y : Fin k → Fin n, span δ y d = span δ (allocOf f δ d) d →
        rank (allocOf f δ d) ≤ rank y)
    (d : Fin n → Fin k → ℝ) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i : Fin n) (m : ℤ)
    (hi : rowLoad δ (allocOf f δ d) d i ≤ δ * (m : ℝ))
    (hfloor : ∀ l : Fin n,
      (∑ _j ∈ Finset.univ.filter (fun j => allocOf f δ d j = l), roundUp δ a) ≤ δ * (m : ℝ)) :
    ∃ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧ v i = d i ∧
      allocOf f δ v = allocOf f δ d ∧ span δ (allocOf f δ d) v ≤ δ * (m : ℝ) := by
  classical
  let x := allocOf f δ d
  let C := δ * (m : ℝ)
  let M := span δ x d
  by_cases hMC : M ≤ C
  · exact ⟨d, hd, rfl, rfl, hMC⟩
  let S (l : Fin n) := Finset.univ.filter (fun j => x j = l)
  have H (l : Fin n) : ∃ v : Fin k → ℝ, (∀ j, a ≤ v j ∧ v j ≤ b) ∧
      (l = i → v = d l) ∧ (∀ j ∉ S l, v j = d l j) ∧
      (∀ j, roundUp δ (v j) ≤ roundUp δ (d l j)) ∧
      (∑ j ∈ S l, roundUp δ (v j)) = min (rowLoad δ x d l) C := by
    by_cases hl : l = i
    · subst l
      exact ⟨d i, hd i, fun _ => rfl, fun _ _ => rfl, fun _ => le_rfl,
        (min_eq_left hi).symm⟩
    · obtain ⟨v, hv, hsupport, hmono, hsum⟩ :=
        cap_row hδ (S l) (d l) (hd l) m (hfloor l)
      exact ⟨v, hv, fun h => (hl h).elim, hsupport, hmono, hsum⟩
  choose v hv hvi hsupport hmono hsum using H
  have hrow (l : Fin n) : rowLoad δ x v l = min (rowLoad δ x d l) C := hsum l
  have hxcap : span δ x v ≤ C := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    rw [hrow]
    exact min_le_right _ _
  have hxold (l : Fin n) : rowLoad δ x d l ≤ M := by
    dsimp only [M]
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ l)
  have cutBound (l : Fin n) : rowLoad δ x d l - rowLoad δ x v l ≤ M - C := by
    rw [hrow]
    rcases le_total (rowLoad δ x d l) C with h | h
    · rw [min_eq_left h, sub_self]
      linarith [lt_of_not_ge hMC]
    · rw [min_eq_right h]
      linarith [hxold l]
  have gain (y : Fin k → Fin n) (l : Fin n) :
      rowLoad δ y d l - rowLoad δ y v l ≤ M - C := by
    let sy := Finset.univ.filter (fun j => y j = l)
    let diff (j : Fin k) := roundUp δ (d l j) - roundUp δ (v l j)
    have hsupportSum : (∑ j ∈ sy, diff j) = ∑ j ∈ sy ∩ S l, diff j := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j hj hfalse
      have hjS : j ∉ S l := fun hh => hfalse (Finset.mem_inter.mpr ⟨hj, hh⟩)
      unfold diff
      rw [hsupport l j hjS, sub_self]
    have hsubset : (∑ j ∈ sy ∩ S l, diff j) ≤ ∑ j ∈ S l, diff j :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun j _ _ => sub_nonneg.mpr (hmono l j))
    calc
      rowLoad δ y d l - rowLoad δ y v l = ∑ j ∈ sy, diff j := by rw [Finset.sum_sub_distrib]; rfl
      _ = ∑ j ∈ sy ∩ S l, diff j := hsupportSum
      _ ≤ ∑ j ∈ S l, diff j := hsubset
      _ = rowLoad δ x d l - rowLoad δ x v l := by rw [Finset.sum_sub_distrib]; rfl
      _ ≤ M - C := cutBound l
  have allgain (y) : span δ y d ≤ span δ y v + (M-C) := by
    rw [span_eq δ y d]
    apply Finset.sup'_le
    intro l _
    have hh : rowLoad δ y v l ≤ span δ y v := by
      rw [span_eq]
      exact Finset.le_sup' _ (Finset.mem_univ l)
    linarith [gain y l]
  let z := allocOf f δ v
  have hzv : span δ z v ≤ span δ x v := (hf k v hv).2 x
  have hzd : M ≤ span δ z d := (hf k d hd).2 z
  have hzM : span δ z v = C := by linarith [allgain z]
  have hxM : span δ x v = C := by linarith
  have hrank₁ : rank z ≤ rank x := hpriority v hv x (hxM.trans hzM.symm)
  have hzdM : span δ z d = M := by linarith [allgain z]
  have hrank₂ : rank x ≤ rank z := hpriority d hd z hzdM
  exact ⟨v, hv, hvi i rfl, hinj (le_antisymm hrank₁ hrank₂), hxcap⟩

private theorem row_le_span {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (i : Fin n) : rowLoad δ x d i ≤ span δ x d := by
  rw [span_eq]
  exact Finset.le_sup' _ (Finset.mem_univ i)

private theorem span_mono {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (u v : Fin n → Fin k → ℝ) (h : ∀ l j, roundUp δ (u l j) ≤ roundUp δ (v l j)) :
    span δ x u ≤ span δ x v := by
  rw [span_eq]
  apply Finset.sup'_le
  intro l _
  exact (Finset.sum_le_sum (fun j _ => h l j)).trans (row_le_span δ x v l)

private theorem certificates_at_one_step {n k : ℕ} [NeZero n] {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i))
    (m : ℤ) (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) ≤ δ * (m : ℝ)) :
    HasAllocationCertificates f δ a b t d (δ * (m : ℝ) + δ) := by
  classical
  let C := δ * (m : ℝ)
  let K := C + δ
  have hCK : C ≤ K := le_add_of_nonneg_right hδ.le
  have hK : K = δ * ((m + 1 : ℤ) : ℝ) := by simp [K, C, mul_add]
  let s (i : Fin n) := Function.update t i (d i)
  let x (i : Fin n) := allocOf f δ (s i)
  let H (i : Fin n) := span δ (x i) (s i)
  have hs (i l : Fin n) (r : Fin k) : a ≤ s i l r ∧ s i l r ≤ b := by
    by_cases hl : l = i
    · subst l; simpa [s] using hd i r
    · simpa [s, hl] using ht l r
  have hsi (i : Fin n) : s i i = d i := by simp [s]
  have hcorr (i : Fin n) : Function.update (s i) i (t i) = t := by simp [s]
  have htrue (i : Fin n) : span δ (x i) t ≤ C := by
    have h : span δ (x i) (Function.update (s i) i (t i)) ≤
        span δ y (Function.update (s i) i (t i)) :=
      hop i (s i) (hs i) (hsi i) y
    rw [hcorr i] at h
    exact h.trans hy
  by_cases hlow : ∀ i, H i ≤ K
  · intro i _
    let S := (Finset.univ : Finset (Fin n)).erase i
    let v := Function.update d i (t i)
    have hev : (fun l : Fin n => if l ∈ S then d l else t l) = v := by
      funext l
      by_cases h : l = i <;> simp [S, v, h]
    have hbound : span δ (allocOf f δ v) v ≤ K := by
      have h := report_subset_optimum_le_singletons f hf t d ht hd hop y (hy.trans hCK) hlow S
      dsimp only at h
      rwa [hev] at h
    exact ⟨d, hd, rfl, rfl, allocOf f δ v, hbound⟩
  have frozen (i : Fin n) (hi : K < H i)
      (v : Fin n → Fin k → ℝ) (hv : ∀ l r, a ≤ v l r ∧ v l r ≤ b) (hvi : v i = d i)
      (hcomp : ∃ z : Fin k → Fin n, span δ z (Function.update v i (t i)) ≤ C) :
      allocOf f δ v = x i ∧ span δ (x i) (Function.update v i (t i)) ≤ C ∧
        span δ (x i) v = H i :=
    fixed_priority_stability_of_large_single_report_gap hab hδ f hf rank hinj hpriority
      t d ht hd i (hop i) m y hy hi v hv hvi hcomp
  have transfer (i l : Fin n) (hi : K < H i) (hl : l ≠ i)
      (z : Fin k → Fin n) (hz : span δ z t ≤ C) :
      rowLoad δ (x i) d l ≤ max C (rowLoad δ z d l) := by
    by_cases hC : rowLoad δ (x i) d l ≤ C
    · exact hC.trans (le_max_left _ _)
    let S := Finset.univ.filter (fun r => z r = l)
    let T := Finset.univ.filter (fun r => x i r = l)
    have hFloor : (∑ _r ∈ S, roundUp δ a) ≤ C :=
      (Finset.sum_le_sum (fun r _ => time_mono hδ (ht l r).1)).trans
        ((row_le_span δ z t l).trans hz)
    have himp (p : Fin k → ℝ) (hp : ∀ r, a ≤ p r ∧ p r ≤ b)
        (hpS : (∑ r ∈ S, roundUp δ (p r)) ≤ C) :
        (∑ r ∈ T, roundUp δ (p r)) ≤ C := by
      let v := Function.update (s i) l p
      have hv (u : Fin n) (r : Fin k) : a ≤ v u r ∧ v u r ≤ b := by
        by_cases hu : u = l
        · subst u; simpa [v] using hp r
        · simpa [v, hu] using hs i u r
      have hvi : v i = d i := by simp [v, Ne.symm hl, hsi]
      let u := Function.update v i (t i)
      have hvEq : u = Function.update t l p := by
        funext j
        by_cases h1 : j = i
        · subst j; simp [u, Ne.symm hl]
        · by_cases h2 : j = l
          · subst j; simp [u, v, hl]
          · simp [u, v, s, h1, h2]
      have hcomp : span δ z u ≤ C := by
        rw [span_eq]
        apply Finset.sup'_le
        intro j _
        by_cases hj : j = l
        · subst j; simpa [rowLoad, hvEq, S] using hpS
        · have hh := (row_le_span δ z t j).trans hz
          simpa [rowLoad, hvEq, hj] using hh
      have h := (row_le_span δ (x i) u l).trans
        (frozen i hi v hv hvi ⟨z, hcomp⟩).2.1
      simpa [rowLoad, hvEq, T] using h
    exact (threshold_implication_controls_rounded_bundle_load hab hδ S T m hFloor himp
      (d l) (hd l) (lt_of_not_ge hC)).trans (le_max_right _ _)
  have xinS (i : Fin n) (z : Fin k → Fin n) :
      rowLoad δ z (s i) i = rowLoad δ z d i := by simp [rowLoad, hsi]
  have oneRowBound (i : Fin n) (z : Fin k → Fin n) (hz : span δ z t ≤ C)
      {U : ℝ} (hCU : C ≤ U) (hzi : rowLoad δ z d i ≤ U) :
      span δ z (s i) ≤ U := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hl : l = i
    · subst l; rwa [xinS]
    · have h := ((row_le_span δ z t l).trans hz).trans hCU
      simpa [rowLoad, s, hl] using h
  have reportSelf (i : Fin n) : rowLoad δ (x i) d i ≤ H i := by
    rw [← xinS i]
    exact row_le_span δ (x i) (s i) i
  have crossOpt (i j : Fin n) (hi : K < H i) (hj : K < H j) (hij : i ≠ j) :
      rank (x i) ≤ rank (x j) := by
    have hCH : C ≤ H i := hCK.trans hi.le
    have hload : rowLoad δ (x j) d i ≤ H i :=
      (transfer j i hj hij (x i) (htrue i)).trans (max_le hCH (reportSelf i))
    have hfit : span δ (x j) (s i) ≤ H i :=
      oneRowBound i (x j) (htrue j) hCH hload
    have hval : span δ (x j) (s i) = H i := le_antisymm hfit ((hf k (s i) (hs i)).2 (x j))
    exact hpriority (s i) (hs i) (x j) hval
  have same (i j : Fin n) (hi : K < H i) (hj : K < H j) : x i = x j := by
    by_cases hij : i = j
    · subst j; rfl
    · exact hinj (le_antisymm (crossOpt i j hi hj hij) (crossOpt j i hj hi (Ne.symm hij)))
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty H
  have hMax (i : Fin n) : H i ≤ H i₀ := (Finset.le_sup' H (Finset.mem_univ i)).trans_eq hmax
  have hHigh : K < H i₀ := by
    by_contra hh
    exact hlow (fun i => (hMax i).trans (le_of_not_gt hh))
  let X := x i₀
  let U := H i₀
  have hCompU : C ≤ U := hCK.trans hHigh.le
  have hXloads (i : Fin n) : rowLoad δ X d i ≤ max C (H i) := by
    by_cases hi : i = i₀
    · subst i; exact (reportSelf i₀).trans (le_max_right _ _)
    · exact (transfer i₀ i hHigh hi (x i) (htrue i)).trans
        (max_le_max le_rfl (reportSelf i))
  have hXd : span δ X d ≤ U := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    exact (hXloads l).trans (max_le hCompU (hMax l))
  let base : Fin n → Fin k → ℝ := Function.update (fun _ _ => a) i₀ (d i₀)
  have hb (l : Fin n) (r : Fin k) : a ≤ base l r ∧ base l r ≤ b := by
    by_cases hl : l = i₀
    · subst l; simpa [base] using hd i₀ r
    · simp [base, hl, hab]
  have hiBase : base i₀ = d i₀ := by simp [base]
  have hbaseTrue : span δ y (Function.update base i₀ (t i₀)) ≤ C := by
    refine (span_mono δ y _ _ (fun l r => ?_)).trans hy
    by_cases hl : l = i₀
    · subst l; simp
    · simpa [base, hl] using time_mono hδ (ht l r).1
  obtain ⟨hbX, _, hXb⟩ := frozen i₀ hHigh base hb hiBase ⟨y, hbaseTrue⟩
  let z := allocOf f δ d
  have hBut : U ≤ span δ z base := by
    have h : span δ (allocOf f δ base) base ≤ span δ z base := (hf k base hb).2 z
    rw [hbX, hXb] at h
    exact h
  have hzMono : span δ z base ≤ span δ z d := by
    apply span_mono
    intro l r
    by_cases hl : l = i₀
    · subst l; simp [base]
    · simpa [base, hl] using time_mono hδ (hd l r).1
  have hzD : span δ z d ≤ span δ X d := (hf k d hd).2 X
  have hXdEq : span δ X d = U := le_antisymm hXd (hBut.trans (hzMono.trans hzD))
  have hzEq : span δ z d = U := le_antisymm (hzD.trans hXd) (hBut.trans hzMono)
  have hzEqB : span δ z base = U := le_antisymm (hzMono.trans_eq hzEq) hBut
  have hfirst : rank z ≤ rank X := hpriority d hd X (hXdEq.trans hzEq.symm)
  have hsecond : rank X ≤ rank z := by
    have he : span δ z base = span δ (allocOf f δ base) base := by rw [hbX, hzEqB, hXb]
    have h := hpriority base hb z he
    simpa only [hbX] using h
  have hzX : z = X := hinj (le_antisymm hfirst hsecond)
  have htrueZ : span δ z t ≤ C := by rw [hzX]; exact htrue i₀
  intro i _
  by_cases hHi : K < H i
  · have hkeep : allocOf f δ (s i) = z := (same i i₀ hHi hHigh).trans hzX.symm
    refine ⟨s i, hs i, hsi i, hkeep, y, ?_⟩
    rw [hcorr i]
    exact hy.trans hCK
  have hld : rowLoad δ z d i ≤ K := by
    rw [hzX]
    exact (hXloads i).trans (max_le hCK (le_of_not_gt hHi))
  have hfloor (l : Fin n) :
      (∑ _r ∈ Finset.univ.filter (fun r => z r = l), roundUp δ a) ≤ K := by
    refine (Finset.sum_le_sum (fun r _ => time_mono hδ (ht l r).1)).trans ?_
    exact ((row_le_span δ z t l).trans htrueZ).trans hCK
  obtain ⟨v, hv, hvi, hzv, hcap⟩ :=
    fixed_priority_cap hδ f hf rank hinj hpriority d hd i (m + 1)
      (hK ▸ hld) (fun l => hK ▸ hfloor l)
  refine ⟨v, hv, hvi, hzv, z, ?_⟩
  change span δ z (Function.update v i (t i)) ≤ K
  rw [span_eq]
  apply Finset.sup'_le
  intro l _
  by_cases hl : l = i
  · subst l
    have h := ((row_le_span δ z t i).trans htrueZ).trans hCK
    simpa [rowLoad] using h
  · have h := (row_le_span δ z v l).trans hcap
    rw [← hK] at h
    simpa [rowLoad, hl] using h


private theorem span_grid {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) : ∃ m : ℤ, span δ x d = δ * (m : ℝ) := by
  rw [span_eq]
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rowLoad δ x d)
  refine ⟨∑ j ∈ Finset.univ.filter (fun j => x j = i), ⌈d i j / δ⌉, h.trans ?_⟩
  simp [rowLoad, roundUp, Finset.mul_sum]

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ a : ℝ, 0 < a → ∃ δ : ℝ,
      0 < δ ∧ δ < a ∧ 2 * δ ≤ ε * a ∧
      ∀ b : ℝ, a < b → ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ k : ℕ, n < k →
        let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
        ∀ t d : Fin n → Fin k → ℝ,
          (∀ l j, a ≤ t l j ∧ t l j ≤ b) →
          (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
          (∀ i, DeclarationOptimal f δ a b i (t i) (d i)) →
          ∀ y : Fin k → Fin n,
            (∃ j, roundUp δ (t (y j) j) < roundUp δ (d (y j) j)) →
            (¬ ∃ (M : ℝ) (c : ℕ), a ≤ M ∧ M ≤ b ∧ roundUp δ M = M ∧
              k - 1 ≤ (n - 2) * c ∧ (c : ℝ) * roundUp δ a < M ∧
              roundedMakespan δ y (corrStar y t) < M ∧
              M ≤ (1 + ε) * makespan y (corrStar y t)) →
            HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by
  classical
  intro ε hε a ha
  let δ := min (a / 2) (ε * a / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ < a := (min_le_left _ _).trans_lt (by linarith)
  have hstep : 2 * δ ≤ ε * a := by linarith [min_le_right (a / 2) (ε * a / 2)]
  refine ⟨δ, hδ, hδa, hstep, ?_⟩
  intro b hab n _ _ k hkn
  dsimp only
  intro t d ht hd hop y _ _
  let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
  obtain ⟨rank, hinj, hpriority⟩ := boundedLoadDP_respects_fixed_priority (b := b) ha hδ n k
  obtain ⟨m, hm⟩ := span_grid δ y t
  have hcert := certificates_at_one_step hab.le hδ f (boundedLoadDP_exact ha hδ n)
    rank hinj hpriority t d ht hd hop m y hm.le
  let T := makespan y (corrStar y t)
  have hT : a ≤ T := by
    let j : Fin k := ⟨0, by omega⟩
    have hh : corrStar y t j ≤ load y (corrStar y t) (y j) := by
      exact Finset.single_le_sum (f := corrStar y t) (fun r _ => ha.le.trans (ht (y r) r).1)
        (by simp)
    exact (ht (y j) j).1.trans (hh.trans (Finset.le_sup' _ (Finset.mem_univ (y j))))
  have hrounded := (rounding_error_bound ha hδ y (corrStar y t) (fun j => (ht (y j) j).1)).2
  have hsub : δ / a ≤ ε - δ / a := (div_le_iff₀ ha).2 (by
    rw [sub_mul, div_mul_cancel₀ _ ha.ne']
    linarith)
  have hunit : 1 ≤ T / a := (le_div_iff₀ ha).2 (by simpa using hT)
  have hadd : δ ≤ (δ / a) * T := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    simpa using mul_le_mul_of_nonneg_left hunit hδ.le
  have hbound : δ * (m : ℝ) + δ ≤ (1 + ε) * T := by
    change roundedMakespan δ y (corrStar y t) = δ * (m : ℝ) at hm
    rw [← hm]
    linarith only [hrounded, hadd, mul_le_mul_of_nonneg_right hsub (ha.le.trans hT)]
  intro i hi
  obtain ⟨v, hv, hvi, hx, z, hz⟩ := hcert i hi
  exact ⟨v, hv, hvi, hx, z, hz.trans hbound⟩
