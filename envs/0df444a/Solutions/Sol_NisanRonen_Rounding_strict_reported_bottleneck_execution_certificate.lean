-- Prove2me | solution 1 for NisanRonen.Rounding.strict_reported_bottleneck_execution_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:33:48.098543+00:00
-- url     : https://prove2.me/submissions/3524bc99-0f14-4659-8800-49863d62e974

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

theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i : Fin n) (hop : DeclarationOptimal f δ a b i (t i) (d i)) (m : ℤ) :
    let x := allocOf f δ d
    roundedMakespan δ x (corrStar x t) ≤ δ * (m : ℝ) →
    δ * (m : ℝ) < (∑ j ∈ Finset.univ.filter (fun j => x j = i), roundUp δ (d i j)) →
    (∀ l ≠ i, (∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)) <
      ∑ j ∈ Finset.univ.filter (fun j => x j = i), roundUp δ (d i j)) →
    ∃ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧
      v i = d i ∧ allocOf f δ v = x ∧
      roundedMakespan δ x (corrStar x (Function.update v i (t i))) ≤ δ * (m : ℝ) := by
  classical
  dsimp only
  intro htrue hbig hstrict
  let x := allocOf f δ d
  let C := δ * (m : ℝ)
  let M := rowLoad δ x d i
  let S (l : Fin n) := Finset.univ.filter (fun j => x j = l)
  change C < M at hbig
  change ∀ l ≠ i, rowLoad δ x d l < M at hstrict
  have htl (l : Fin n) : rowLoad δ x t l ≤ C := by
    refine le_trans ?_ htrue
    change rowLoad δ x t l ≤ span δ x t
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ l)
  have hfloor (l : Fin n) : (∑ _j ∈ S l, roundUp δ a) ≤ C :=
    (Finset.sum_le_sum (fun j _ => time_mono hδ (ht l j))).trans (htl l)
  have rows (l : Fin n) : ∃ row : Fin k → ℝ,
      (∀ j, a ≤ row j ∧ row j ≤ b) ∧
      (l = i → row = d l) ∧ (∀ j ∉ S l, row j = d l j) ∧
      (∀ j, roundUp δ (row j) ≤ roundUp δ (d l j)) ∧
      (l ≠ i → (∑ j ∈ S l, roundUp δ (row j)) = min (rowLoad δ x d l) C) := by
    by_cases hl : l = i
    · exact ⟨d l, hd l, fun _ => rfl, fun _ _ => rfl, fun _ => le_rfl, fun h => (h hl).elim⟩
    · obtain ⟨row, hrow, hout, hmono, hsum⟩ := cap_row hδ (S l) (d l) (hd l) m (hfloor l)
      exact ⟨row, hrow, fun h => (hl h).elim, hout, hmono, fun _ => hsum⟩
  choose v hv hvi hout hmono hsum using rows
  have hv_i : v i = d i := hvi i rfl
  have hxrow (l : Fin n) (hl : l ≠ i) :
      rowLoad δ x v l = min (rowLoad δ x d l) C := hsum l hl
  let v' := Function.update v i (t i)
  have hxc : span δ x v' ≤ C := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hl : l = i
    · subst l
      simpa [rowLoad, v'] using htl i
    · have hh : rowLoad δ x v l ≤ C := by rw [hxrow l hl]; exact min_le_right _ _
      simpa [rowLoad, v', hl] using hh
  let z := allocOf f δ v
  have hzc : span δ z v' ≤ C := (hop v hv hv_i x).trans hxc
  have gain (y : Fin k → Fin n) (l : Fin n) :
      rowLoad δ y d l - rowLoad δ y v l ≤ rowLoad δ x d l - rowLoad δ x v l := by
    let sy := Finset.univ.filter (fun j => y j = l)
    let diff (j : Fin k) := roundUp δ (d l j) - roundUp δ (v l j)
    have hsupportSum : (∑ j ∈ sy, diff j) = ∑ j ∈ sy ∩ S l, diff j := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro j hj hfalse
      have hjS : j ∉ S l := fun hh => hfalse (Finset.mem_inter.mpr ⟨hj, hh⟩)
      unfold diff
      rw [hout l j hjS, sub_self]
    have hsubset : (∑ j ∈ sy ∩ S l, diff j) ≤ ∑ j ∈ S l, diff j :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun j _ _ => sub_nonneg.mpr (hmono l j))
    calc
      rowLoad δ y d l - rowLoad δ y v l = ∑ j ∈ sy, diff j := by rw [Finset.sum_sub_distrib]; rfl
      _ = ∑ j ∈ sy ∩ S l, diff j := hsupportSum
      _ ≤ ∑ j ∈ S l, diff j := hsubset
      _ = rowLoad δ x d l - rowLoad δ x v l := by rw [Finset.sum_sub_distrib]; rfl
  have hzo (l : Fin n) (hl : l ≠ i) : rowLoad δ z v l ≤ C := by
    have h : rowLoad δ z v' l ≤ span δ z v' := by
      rw [span_eq]
      exact Finset.le_sup' _ (Finset.mem_univ l)
    simpa [rowLoad, v', hl] using h.trans hzc
  have hzoOld (l : Fin n) (hl : l ≠ i) : rowLoad δ z d l < M := by
    have hbound := gain z l
    rw [hxrow l hl] at hbound
    rcases le_total (rowLoad δ x d l) C with h | h
    · rw [min_eq_left h, sub_self] at hbound
      linarith [hzo l hl]
    · rw [min_eq_right h] at hbound
      linarith [hstrict l hl, hzo l hl]
  have span_x_old : span δ x d = M := by
    rw [span_eq]
    refine le_antisymm (Finset.sup'_le _ _ ?_) (Finset.le_sup' (rowLoad δ x d) (Finset.mem_univ i))
    intro l _
    by_cases hl : l = i
    · simp [hl, M]
    · exact (hstrict l hl).le
  have span_x_new : span δ x v = M := by
    rw [span_eq]
    have hi : rowLoad δ x v i = M := by simp [rowLoad, hv_i, M]
    refine le_antisymm (Finset.sup'_le _ _ ?_) (hi ▸ Finset.le_sup' _ (Finset.mem_univ i))
    intro l _
    by_cases hl : l = i
    · simpa [hl] using hi.le
    · rw [hxrow l hl]
      exact (min_le_right _ _).trans hbig.le
  have h_z_d : rowLoad δ z d i ≤ M := by
    have h := Finset.le_sup' (rowLoad δ z v) (Finset.mem_univ i)
    rw [← span_eq] at h
    have hvmin : span δ z v ≤ M := ((hf k v hv).2 x).trans_eq span_x_new
    simpa [rowLoad, hv_i] using h.trans hvmin
  have hy : span δ z d = M := by
    refine le_antisymm ?_ (span_x_old ▸ (hf k d hd).2 z)
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hl : l = i
    · simpa [hl] using h_z_d
    · exact (hzoOld l hl).le
  have hzi : rowLoad δ z d i = M := by
    by_contra hne
    have hlt : rowLoad δ z d i < M := lt_of_le_of_ne h_z_d hne
    have h : span δ z d < M := by
      rw [span_eq]
      apply (Finset.sup'_lt_iff _).2
      intro l _
      by_cases hl : l = i
      · simpa [hl] using hlt
      · exact hzoOld l hl
    rw [hy] at h
    exact (lt_irrefl _ h)
  have hzv : span δ z v = M := by
    refine le_antisymm (((hf k v hv).2 x).trans_eq span_x_new) ?_
    have he : rowLoad δ z v i = M := by simpa [rowLoad, hv_i] using hzi
    rw [span_eq, ← he]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  have h1 : rank z ≤ rank x := hpriority v hv x (span_x_new.trans hzv.symm)
  have h2 : rank x ≤ rank z := hpriority d hd z (hy.trans span_x_old.symm)
  exact ⟨v, hv, hv_i, hinj (le_antisymm h1 h2), hxc⟩
