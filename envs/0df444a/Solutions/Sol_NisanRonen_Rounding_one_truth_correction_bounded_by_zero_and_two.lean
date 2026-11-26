-- Prove2me | solution 1 for NisanRonen.Rounding.one_truth_correction_bounded_by_zero_and_two
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T08:02:13.690909+00:00
-- url     : https://prove2.me/submissions/30d5340c-6476-4800-99db-71a7c7775972

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

private theorem row_le_span {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (i : Fin n) : rowLoad δ x d i ≤ span δ x d := by
  rw [span_eq]
  exact Finset.le_sup' _ (Finset.mem_univ i)

private theorem span_grid {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) : ∃ m : ℤ, span δ x d = δ * (m : ℝ) := by
  rw [span_eq]
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rowLoad δ x d)
  refine ⟨∑ j ∈ Finset.univ.filter (fun j => x j = i), ⌈d i j / δ⌉, h.trans ?_⟩
  simp [rowLoad, roundUp, Finset.mul_sum]

theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i j : Fin n) (hij : i ≠ j)
    (hi : DeclarationOptimal f δ a b i (t i) (d i))
    (hj : DeclarationOptimal f δ a b j (t j) (d j)) (y : Fin k → Fin n) :
    let x := allocOf f δ d
    let di := Function.update d i (t i)
    let dij := Function.update di j (t j)
    roundedMakespan δ x (corrStar x di) ≤
      max (roundedMakespan δ x (corrStar x d))
        (roundedMakespan δ y (corrStar y dij)) + δ := by
  classical
  dsimp only
  let x := allocOf f δ d
  let di := Function.update d i (t i)
  let dij := Function.update di j (t j)
  let u := allocOf f δ di
  let D := span δ x d
  let M := span δ u di
  let C := span δ y dij
  change span δ x di ≤ max D C + δ
  have hdi (l : Fin n) (r : Fin k) : a ≤ di l r ∧ di l r ≤ b := by
    by_cases h : l = i
    · subst l; simpa [di] using ht i r
    · simpa [di, h] using hd l r
  have hdi_j : di j = d j := by simp [di, Ne.symm hij]
  have hEq : span δ x di = M :=
    le_antisymm (hi d hd rfl u) ((hf k di hdi).2 x)
  rw [hEq]
  by_contra hfail
  have hM : max D C + δ < M := lt_of_not_ge hfail
  let K := M - δ
  have hDK : D < K := by linarith [(le_max_left D C)]
  have hCK : C < K := by linarith [(le_max_right D C)]
  have hKM : K < M := by linarith
  obtain ⟨m, hm⟩ := span_grid δ u di
  have hKgrid : K = δ * ((m - 1 : ℤ) : ℝ) := by
    change M = _ at hm
    simp [K, hm, mul_sub]
  have hU : span δ u dij ≤ C := hj di hdi hdi_j y
  have otherOnU (l : Fin n) (hl : l ≠ j) : rowLoad δ u di l ≤ C := by
    have h := (row_le_span δ u dij l).trans hU
    simpa [rowLoad, dij, hl] using h
  let S := Finset.univ.filter (fun r => u r = j)
  have hFloor : (∑ _r ∈ S, roundUp δ a) ≤ K := by
    have hh : (∑ _r ∈ S, roundUp δ a) ≤ rowLoad δ u dij j := by
      exact Finset.sum_le_sum (fun r _ => time_mono hδ (by simpa [dij] using (ht j r).1))
    exact (hh.trans ((row_le_span δ u dij j).trans hU)).trans hCK.le
  obtain ⟨rj, hrj, hOutside, hMono, hSum⟩ :=
    cap_row hδ S (d j) (hd j) (m - 1) (hKgrid ▸ hFloor)
  let v := Function.update d j rj
  let vi := Function.update v i (t i)
  have hv (l : Fin n) (r : Fin k) : a ≤ v l r ∧ v l r ≤ b := by
    by_cases h : l = j
    · subst l; simpa [v] using hrj r
    · simpa [v, h] using hd l r
  have hv_i : v i = d i := by simp [v, hij]
  have hvi_j : vi j = rj := by simp [vi, v, Ne.symm hij]
  have hSame (l : Fin n) (hl : l ≠ j) : vi l = di l := by
    by_cases h : l = i
    · subst l; simp [di, vi]
    · simp [di, vi, v, h, hl]
  have hSum' : rowLoad δ u vi j = min (rowLoad δ u di j) K := by
    rw [rowLoad, hvi_j, hSum, ← hKgrid]
    simp [rowLoad, S, hdi_j]
  have hCapU : span δ u vi ≤ K := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hl : l = j
    · subst l; exact hSum'.trans_le (min_le_right _ _)
    · have h := (otherOnU l hl).trans hCK.le
      simpa [rowLoad, hSame l hl] using h
  let z := allocOf f δ v
  have hCapZ : span δ z vi ≤ K := (hi v hv hv_i u).trans hCapU
  have hOtherZ (l : Fin n) (hl : l ≠ j) : rowLoad δ z di l ≤ K := by
    have h := (row_le_span δ z vi l).trans hCapZ
    simpa [rowLoad, hSame l hl] using h
  have hOld : M ≤ span δ z di := (hf k di hdi).2 z
  have hOldJ : M ≤ rowLoad δ z di j := by
    by_contra hb
    have hs : span δ z di < M := by
      rw [span_eq]
      apply (Finset.sup'_lt_iff _).2
      intro l _
      by_cases hl : l = j
      · subst l; exact lt_of_not_ge hb
      · exact (hOtherZ l hl).trans_lt hKM
    exact (not_lt_of_ge hOld) hs
  have reduction (w : Fin k → Fin n) :
      rowLoad δ w di j - rowLoad δ w vi j ≤ rowLoad δ u di j - rowLoad δ u vi j := by
    let T := Finset.univ.filter (fun r => w r = j)
    let diff (r : Fin k) := roundUp δ (d j r) - roundUp δ (rj r)
    have hs : (∑ r ∈ T, diff r) = ∑ r ∈ T ∩ S, diff r := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro r hr hmiss
      have hn : r ∉ S := fun h => hmiss (Finset.mem_inter.mpr ⟨hr, h⟩)
      simp [diff, hOutside r hn]
    have hsub : (∑ r ∈ T ∩ S, diff r) ≤ ∑ r ∈ S, diff r :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun r _ _ => sub_nonneg.mpr (hMono r))
    have hv := hs.trans_le hsub
    simpa only [diff, Finset.sum_sub_distrib, rowLoad, T, S, hdi_j, hvi_j] using hv
  have hReductionU : rowLoad δ u di j - rowLoad δ u vi j ≤ M - K := by
    rw [hSum']
    rcases le_total (rowLoad δ u di j) K with h | h
    · rw [min_eq_left h, sub_self]
      linarith
    · rw [min_eq_right h]
      linarith [row_le_span δ u di j]
  have hNewJ : K ≤ rowLoad δ z vi j := by
    linarith only [hOldJ, reduction z, hReductionU]
  have hNewReported : K ≤ span δ z v := by
    have hjv : vi j = v j := by simp [vi, Ne.symm hij]
    refine hNewJ.trans_eq ?_ |>.trans (row_le_span δ z v j)
    simp [rowLoad, hjv]
  have hDown : span δ x v ≤ D := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    refine le_trans (b := rowLoad δ x d l) ?_ (row_le_span δ x d l)
    apply Finset.sum_le_sum
    intro r _
    by_cases hl : l = j
    · subst l; simpa [v] using hMono r
    · simp [v, hl]
  exact (not_le_of_gt hDK) (hNewReported.trans (((hf k v hv).2 x).trans hDown))
