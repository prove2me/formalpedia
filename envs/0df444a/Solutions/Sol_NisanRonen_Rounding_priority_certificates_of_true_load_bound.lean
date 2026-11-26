-- Prove2me | solution 1 for NisanRonen.Rounding.priority_certificates_of_true_load_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:49:45.451582+00:00
-- url     : https://prove2.me/submissions/afc94535-51f8-4a34-a81f-8bc23521f132

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

private theorem fixed_priority_isolate {n k : ℕ} [NeZero n] {a b δ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hprio : ∀ d : Fin n → Fin k → ℝ, (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
      ∀ y : Fin k → Fin n, span δ y d = span δ (allocOf f δ d) d →
        rank (allocOf f δ d) ≤ rank y)
    (d : Fin n → Fin k → ℝ) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b) (i : Fin n)
    (hupper : rowLoad δ (allocOf f δ d) d i ≤ roundUp δ b)
    (hfloor : ∀ l ≠ i,
      (∑ _j ∈ Finset.univ.filter (fun j => allocOf f δ d j = l), roundUp δ a) ≤
        rowLoad δ (allocOf f δ d) d i) :
    ∃ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧ v i = d i ∧
      allocOf f δ v = allocOf f δ d ∧
      (∀ l ≠ i, rowLoad δ (allocOf f δ d) v l =
        ∑ _j ∈ Finset.univ.filter (fun j => allocOf f δ d j = l), roundUp δ a) := by
  classical
  let x := allocOf f δ d
  let v : Fin n → Fin k → ℝ := fun l j => if l = i then d l j else if x j = l then a else b
  have hv (l : Fin n) (j : Fin k) : a ≤ v l j ∧ v l j ≤ b := by
    by_cases hli : l = i <;> by_cases hxj : x j = l <;> simp [v, hli, hxj, hd, hab]
  have hnonneg (u : ℝ) (hu : a ≤ u) : 0 ≤ roundUp δ u :=
    (ha.le.trans hu).trans (time_ge hδ)
  have hpos (u : ℝ) (hu : a ≤ u) : 0 < roundUp δ u :=
    (ha.trans_le hu).trans_le (time_ge hδ)
  have hvi : v i = d i := by funext j; simp [v]
  have hvl (l : Fin n) (hl : l ≠ i) : rowLoad δ x v l =
      ∑ _j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ a := by
    unfold rowLoad
    apply Finset.sum_congr rfl
    intro j hj
    simp [v, hl, (Finset.mem_filter.1 hj).2]
  let D := rowLoad δ x d i
  let M := span δ x d
  have hdi : D ≤ M := by
    change rowLoad δ x d i ≤ span δ x d
    rw [span_eq]
    exact Finset.le_sup' (rowLoad δ x d) (Finset.mem_univ i)
  have hxv : span δ x v ≤ D := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hl : l = i
    · subst l
      exact le_of_eq (by simp [rowLoad, hvi, D])
    · rw [hvl l hl]
      exact hfloor l hl
  have hloadle (y : Fin k → Fin n) (l : Fin n) :
    rowLoad δ y v l ≤ span δ y v := by
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ l)
  have hadded (y : Fin k → Fin n) (l : Fin n) (hli : l ≠ i) (j : Fin k)
      (hjl : y j = l) (hxj : x j ≠ l) : roundUp δ b ≤ rowLoad δ y v l := by
    have hjmem : j ∈ Finset.univ.filter (fun j => y j = l) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ j, hjl⟩
    have hs := Finset.single_le_sum (f := fun j => roundUp δ (v l j))
      (fun j _ => hnonneg _ (hv l j).1) hjmem
    simpa [rowLoad, v, hli, hxj] using hs
  have hall (y : Fin k → Fin n) : D ≤ span δ y v := by
    by_cases hset : ∀ j, x j = i → y j = i
    · have hsub : Finset.univ.filter (fun j => x j = i) ⊆
          Finset.univ.filter (fun j => y j = i) := by
        intro j hj
        exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hset j (Finset.mem_filter.1 hj).2⟩
      have hh : D ≤ rowLoad δ y v i := by
        unfold D rowLoad
        rw [hvi]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnonneg _ (hd i j).1)
      exact hh.trans (hloadle y i)
    · push Not at hset
      obtain ⟨j, hxj, hyj⟩ := hset
      have hxne : x j ≠ y j := by rw [hxj]; exact Ne.symm hyj
      exact hupper.trans ((hadded y (y j) hyj j rfl hxne).trans (hloadle y (y j)))
  have hvold (y : Fin k → Fin n) (hyw : span δ y v ≤ D) : span δ y d ≤ M := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hli : l = i
    · subst l
      have hh : rowLoad δ y d i = rowLoad δ y v i := by simp [rowLoad, hvi]
      rw [hh]
      exact (hloadle y i).trans (hyw.trans hdi)
    · by_cases hs : ∀ j, y j = l → x j = l
      · have hsub : Finset.univ.filter (fun j => y j = l) ⊆
          Finset.univ.filter (fun j => x j = l) := by
          intro j hj
          exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hs j (Finset.mem_filter.1 hj).2⟩
        have ho : rowLoad δ x d l ≤ M := by
          dsimp only [M]
          rw [span_eq]
          exact Finset.le_sup' _ (Finset.mem_univ l)
        refine le_trans ?_ ho
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnonneg _ (hd l j).1)
      · push Not at hs
        obtain ⟨j, hjl, hxj⟩ := hs
        let S := Finset.univ.filter (fun j => y j = l)
        have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ j, hjl⟩
        have hvj : v l j = b := by simp [v, hli, hxj]
        have hB : roundUp δ b ≤ D := (hadded y l hli j hjl hxj).trans ((hloadle y l).trans hyw)
        have hs₁ : S = {j} := by
          apply le_antisymm
          · intro jr hjr
            rw [Finset.mem_singleton]
            by_contra hne
            have hsub : ({j, jr} : Finset (Fin k)) ⊆ S := by
              intro jj hjj
              simp only [Finset.mem_insert, Finset.mem_singleton] at hjj
              rcases hjj with rfl | rfl
              · exact hjS
              · exact hjr
            have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => roundUp δ (v l j))
              hsub (fun j _ _ => hnonneg _ (hv l j).1)
            rw [Finset.sum_insert (by simpa using Ne.symm hne), Finset.sum_singleton, hvj] at hsum
            have hhigh : roundUp δ b + roundUp δ (v l jr) ≤ D :=
              hsum.trans ((hloadle y l).trans hyw)
            linarith [hpos _ (hv l jr).1]
          · simpa using hjS
        change (∑ j ∈ S, roundUp δ (d l j)) ≤ M
        rw [hs₁, Finset.sum_singleton]
        exact (time_mono hδ (hd l j).2).trans (hB.trans hdi)
  let z := allocOf f δ v
  have hz : span δ z v ≤ span δ x v := (hf k v hv).2 x
  have hzv : span δ z v = D := le_antisymm (hz.trans hxv) (hall z)
  have hxv' : span δ x v = D := le_antisymm hxv (hall x)
  have hzM : span δ z d = M := le_antisymm (hvold z hzv.le) ((hf k d hd).2 z)
  have h₁ := hprio v hv x (hxv'.trans hzv.symm)
  have h₂ := hprio d hd z hzM
  exact ⟨v, hv, hvi, hinj (le_antisymm h₁ h₂), hvl⟩

theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n,
        roundedMakespan δ y (corrStar y v) =
          roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b) (m : ℤ)
    (htrue : roundedMakespan δ (allocOf f δ d) (corrStar (allocOf f δ d) t) ≤ δ * (m : ℝ))
    (hload : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => allocOf f δ d j = i), roundUp δ (d i j)) ≤
        max (δ * (m : ℝ)) (roundUp δ b) ∨
      ∀ l ≠ i,
        (∑ j ∈ Finset.univ.filter (fun j => allocOf f δ d j = l), roundUp δ (d l j)) ≤ δ * (m : ℝ)) :
    HasAllocationCertificates f δ a b t d (δ * (m : ℝ)) := by
  classical
  let x := allocOf f δ d
  let C := δ * (m : ℝ)
  let B := roundUp δ b
  have htl (l : Fin n) : rowLoad δ x t l ≤ C := by
    refine le_trans ?_ htrue
    change rowLoad δ x t l ≤ span δ x t
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ l)
  have hfloor (l : Fin n) :
      (∑ _j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ a) ≤ C := by
    refine le_trans ?_ (htl l)
    exact Finset.sum_le_sum (fun j _ => time_mono hδ (ht l j))
  intro i _
  have hmake (v : Fin n → Fin k → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b)
      (hvi : v i = d i) (hxv : allocOf f δ v = x)
      (hvl : ∀ l ≠ i, rowLoad δ x v l ≤ C) :
      ∃ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧ v i = d i ∧
        allocOf f δ v = x ∧ ∃ y : Fin k → Fin n,
          roundedMakespan δ y (corrStar y (Function.update v i (t i))) ≤ C := by
    refine ⟨v, hv, hvi, hxv, x, ?_⟩
    change span δ x (Function.update v i (t i)) ≤ C
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hl : l = i
    · subst l
      simpa [rowLoad] using htl i
    · simpa [rowLoad, Function.update_of_ne hl] using hvl l hl
  by_cases hi : rowLoad δ x d i ≤ C
  · obtain ⟨v, hv, hvi, hxv, hvc⟩ :=
      fixed_priority_cap hδ f hf rank hinj hpriority d hd i m hi hfloor
    apply hmake v hv hvi hxv
    intro l _
    refine le_trans ?_ hvc
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ l)
  · rcases hload i with hB | hother
    · have hMax : max C B = B := max_eq_right (by
        by_contra hh
        exact hi (hB.trans_eq (max_eq_left (le_of_not_ge hh))))
      have hDb : rowLoad δ x d i ≤ B := hMax ▸ hB
      obtain ⟨v, hv, hvi, hxv, hvol⟩ :=
        fixed_priority_isolate ha hab hδ f hf rank hinj hpriority d hd i hDb
          (fun l _ => (hfloor l).trans (le_of_not_ge hi))
      exact hmake v hv hvi hxv (fun l hl => (hvol l hl).le.trans (hfloor l))
    · exact hmake d hd rfl rfl hother
