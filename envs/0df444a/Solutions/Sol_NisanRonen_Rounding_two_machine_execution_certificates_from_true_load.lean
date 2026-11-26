-- Prove2me | solution 1 for NisanRonen.Rounding.two_machine_execution_certificates_from_true_load
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:42:24.018609+00:00
-- url     : https://prove2.me/submissions/374b4aec-8ac7-41d1-8d5c-9bd463468d43

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

private theorem capped_with_all_positive_drops {k : ℕ} {a b δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin k)) (row : Fin k → ℝ) (hrow : ∀ j, a ≤ row j ∧ row j ≤ b)
    (m : ℤ) (hfloor : (∑ _j ∈ S, roundUp δ a) ≤ δ * (m : ℝ))
    (hroom : δ * ((m + (S.card : ℤ) : ℤ) : ℝ) ≤ ∑ j ∈ S, roundUp δ (row j)) :
    ∃ v : Fin k → ℝ, (∀ j, a ≤ v j ∧ v j ≤ b) ∧ (∀ j ∉ S, v j = row j) ∧
      (∀ j, roundUp δ (v j) ≤ roundUp δ (row j)) ∧
      (∀ j ∈ S, roundUp δ a < roundUp δ (row j) →
        roundUp δ (v j) < roundUp δ (row j)) ∧
      (∑ j ∈ S, roundUp δ (v j)) = δ * (m : ℝ) := by
  classical
  let L : ℤ := ⌈a / δ⌉
  let U (j : Fin k) : ℤ := ⌈row j / δ⌉
  let u (j : Fin k) := if j ∈ S ∧ L < U j then δ * ((U j - 1 : ℤ) : ℝ) else row j
  have hul (j : Fin k) (h : j ∈ S ∧ L < U j) :
      a ≤ δ * ((U j - 1 : ℤ) : ℝ) := (time_ge hδ).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Int.le_sub_one_of_lt h.2) hδ.le)
  have huUpper (j : Fin k) : δ * ((U j - 1 : ℤ) : ℝ) < row j := by
    have h := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (row j / δ)) hδ
    rw [mul_add, mul_one, mul_comm δ (row j / δ), div_mul_cancel₀ _ hδ.ne'] at h
    dsimp only [U]
    push_cast
    linarith
  have hu (j : Fin k) : a ≤ u j ∧ u j ≤ b := by
    by_cases h : j ∈ S ∧ L < U j
    · simpa [u, h] using And.intro (hul j h) ((huUpper j).le.trans (hrow j).2)
    · simpa [u, h] using hrow j
  have humono (j : Fin k) : roundUp δ (u j) ≤ roundUp δ (row j) := by
    apply time_mono hδ
    by_cases h : j ∈ S ∧ L < U j
    · simpa [u, h] using (huUpper j).le
    · simp [u, h]
  have hudrop (j : Fin k) : roundUp δ (row j) - δ ≤ roundUp δ (u j) := by
    by_cases h : j ∈ S ∧ L < U j
    · rw [show u j = δ * ((U j - 1 : ℤ) : ℝ) by simp [u, h], time_grid hδ]
      simp [U, roundUp, mul_sub]
    · simpa [u, h] using sub_le_self (roundUp δ (row j)) hδ.le
  have hs : δ * (m : ℝ) ≤ ∑ j ∈ S, roundUp δ (u j) := by
    have hh : (∑ j ∈ S, (roundUp δ (row j) - δ)) ≤ ∑ j ∈ S, roundUp δ (u j) :=
      Finset.sum_le_sum (fun j _ => hudrop j)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hh
    push_cast at hroom
    rw [mul_add] at hroom
    linarith
  obtain ⟨v, hv, hvs, hvm, hvsum⟩ := cap_row hδ S u hu m hfloor
  refine ⟨v, hv, fun j hj => (hvs j hj).trans (by simp [u, hj]),
    fun j => (hvm j).trans (humono j), ?_, hvsum.trans (min_eq_right hs)⟩
  intro j hj hlt
  have hLU : L < U j := by
    exact_mod_cast (lt_of_mul_lt_mul_left hlt hδ.le)
  refine (hvm j).trans_lt ?_
  rw [show u j = δ * ((U j - 1 : ℤ) : ℝ) by simp [u, hj, hLU], time_grid hδ]
  unfold roundUp
  apply mul_lt_mul_of_pos_left _ hδ
  dsimp [U]
  push_cast
  linarith

private theorem sums_difference {α : Type} [DecidableEq α] (S T : Finset α) (r : α → ℝ) :
    (∑ j ∈ T, r j) - (∑ j ∈ S, r j) =
      (∑ j ∈ T \ S, r j) - (∑ j ∈ S \ T, r j) := by
  have hs : S \ (S ∩ T) = S \ T := by ext j; simp [Finset.mem_sdiff]
  have ht : T \ (S ∩ T) = T \ S := by ext j; simp [Finset.mem_sdiff]
  have h₁ := Finset.sum_sdiff (f := r) (Finset.inter_subset_left : S ∩ T ⊆ S)
  have h₂ := Finset.sum_sdiff (f := r) (Finset.inter_subset_right : S ∩ T ⊆ T)
  rw [hs] at h₁
  rw [ht] at h₂
  linarith only [h₁, h₂]

private theorem span_two_rows {k : ℕ} (δ : ℝ) (x : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i o : Fin 2) (hcover : ∀ l, l = i ∨ l = o) :
    span δ x d = max (rowLoad δ x d i) (rowLoad δ x d o) := by
  rw [span_eq]
  apply le_antisymm
  · apply Finset.sup'_le
    intro l _
    rcases hcover l with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' _ (Finset.mem_univ i)) (Finset.le_sup' _ (Finset.mem_univ o))

private theorem certificates_at_grid_plus_job_count {k : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin 2 → ℕ) → List (Fin 2)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin 2) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin 2 → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin 2, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin 2 → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i)) (m : ℤ) (jobCap : ℕ) :
    let x := allocOf f δ d
    roundedMakespan δ x (corrStar x t) ≤ δ * (m : ℝ) →
    (∀ l, (Finset.univ.filter (fun j => x j = l)).card ≤ jobCap) →
    HasAllocationCertificates f δ a b t d (δ * ((m + (jobCap : ℤ) : ℤ) : ℝ)) := by
  classical
  dsimp only
  intro htrue hcount i _
  let x := allocOf f δ d
  let C := δ * (m : ℝ)
  let m' := m + (jobCap : ℤ)
  let C' := δ * (m' : ℝ)
  have hCC' : C ≤ C' := by
    apply mul_le_mul_of_nonneg_left _ hδ.le
    simp [m']
  let o : Fin 2 := if i = 0 then 1 else 0
  have ho : o ≠ i := by fin_cases i <;> decide
  have cover (l : Fin 2) : l = i ∨ l = o := by fin_cases i <;> fin_cases l <;> decide
  let S (l : Fin 2) := Finset.univ.filter (fun j => x j = l)
  let U := rowLoad δ x d i
  have htrueRow (l : Fin 2) : rowLoad δ x t l ≤ C := by
    refine le_trans ?_ htrue
    change rowLoad δ x t l ≤ span δ x t
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ l)
  have hfloor (l : Fin 2) : (∑ _j ∈ S l, roundUp δ a) ≤ C :=
    (Finset.sum_le_sum (fun j _ => time_mono hδ (ht l j))).trans (htrueRow l)
  have make (v : Fin 2 → Fin k → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b) (hvi : v i = d i)
      (hxv : allocOf f δ v = x) (hvo : rowLoad δ x v o ≤ C') :
      ∃ v : Fin 2 → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧ v i = d i ∧
        allocOf f δ v = x ∧ ∃ y : Fin k → Fin 2,
          span δ y (Function.update v i (t i)) ≤ C' := by
    refine ⟨v, hv, hvi, hxv, x, ?_⟩
    rw [span_two_rows _ _ _ i o cover]
    exact max_le (by simpa [rowLoad] using (htrueRow i).trans hCC')
      (by simpa [rowLoad, ho] using hvo)
  by_cases hsmall : U ≤ C'
  · obtain ⟨v, hv, hvi, hxv, hspan⟩ :=
      fixed_priority_cap hδ f hf rank hinj hpriority d hd i m' hsmall
        (fun l => (hfloor l).trans hCC')
    apply make v hv hvi hxv
    refine le_trans ?_ hspan
    rw [span_eq]
    exact Finset.le_sup' _ (Finset.mem_univ o)
  have hCU : C < U := hCC'.trans_lt (lt_of_not_ge hsmall)
  let um : ℤ := ∑ j ∈ S i, ⌈d i j / δ⌉
  have hu : U = δ * (um : ℝ) := by
    simp [U, rowLoad, S, um, roundUp, Int.cast_sum, Finset.mul_sum]
  obtain ⟨v, hv, hvi, hxv, hspan⟩ :=
    fixed_priority_cap hδ f hf rank hinj hpriority d hd i um
      (le_of_eq hu) (fun l => (hfloor l).trans (hCU.le.trans_eq hu))
  let w (l : Fin 2) (j : Fin k) := if j ∈ S l ∨ l = i then v l j else b
  have hw (l : Fin 2) (j : Fin k) : a ≤ w l j ∧ w l j ≤ b := by
    by_cases h : j ∈ S l ∨ l = i <;> simp [w, h, hv, hab]
  have hwi : w i = d i := by
    funext j
    simp [w, ← hvi]
  have wsame (l : Fin 2) : rowLoad δ x w l = rowLoad δ x v l := by
    unfold rowLoad
    apply Finset.sum_congr rfl
    intro j hj
    rw [show w l j = v l j by simp [w, Or.inl (show j ∈ S l from hj)]]
  have hWU : span δ x w = U := by
    rw [span_two_rows _ _ _ i o cover, wsame, wsame]
    have hi : rowLoad δ x v i = U := by rw [rowLoad, hvi]; rfl
    have ho' : rowLoad δ x v o ≤ U := by
      rw [← hu] at hspan
      rw [span_two_rows _ _ _ i o cover] at hspan
      exact (le_max_right _ _).trans hspan
    rw [hi, max_eq_left ho']
  have wmono (z : Fin k → Fin 2) : span δ z v ≤ span δ z w := by
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    refine le_trans (b := rowLoad δ z w l) ?_ ?_
    · apply Finset.sum_le_sum
      intro j _
      apply time_mono hδ
      by_cases h : j ∈ S l ∨ l = i <;> simp [w, h, hv]
    · rw [span_eq]
      exact Finset.le_sup' (rowLoad δ z w) (Finset.mem_univ l)
  have hxw : allocOf f δ w = x := by
    let z := allocOf f δ w
    have hzW : span δ z w ≤ U := ((hf k w hw).2 x).trans_eq hWU
    have hvU : span δ x v = U := by
      symm
      rw [← hWU, span_two_rows _ _ _ i o cover, span_two_rows _ _ _ i o cover, wsame, wsame]
    have hOld : U ≤ span δ z v := by
      have h : span δ (allocOf f δ v) v ≤ span δ z v := (hf k v hv).2 z
      rw [hxv, hvU] at h
      exact h
    have hvEq : span δ z v = U := le_antisymm ((wmono z).trans hzW) hOld
    have hwEq : span δ z w = U := le_antisymm hzW (hOld.trans (wmono z))
    apply hinj
    apply le_antisymm
    · exact hpriority w hw x (hWU.trans hwEq.symm)
    · have he : span δ z v = span δ (allocOf f δ v) v := by
        rw [hxv, hvEq, hvU]
      have h := hpriority v hv z he
      rw [hxv] at h
      exact h
  let L := rowLoad δ x w o
  have hLU : L ≤ U := by
    rw [span_two_rows _ _ _ i o cover] at hWU
    exact (le_max_right _ _).trans_eq hWU
  by_cases hlo : L ≤ C
  · exact make w hw hwi hxw (hlo.trans hCC')
  have newRow :
      ∃ q : Fin k → ℝ, (∀ j, a ≤ q j ∧ q j ≤ b) ∧ (∀ j ∉ S o, q j = b) ∧
        (∀ j, roundUp δ (q j) ≤ roundUp δ (w o j)) ∧
        (L = U → ∀ j ∈ S o, roundUp δ a < roundUp δ (w o j) →
          roundUp δ (q j) < roundUp δ (w o j)) ∧
        (∑ j ∈ S o, roundUp δ (q j)) = C := by
    have outside (j : Fin k) (hj : j ∉ S o) : w o j = b := by simp [w, hj, ho]
    by_cases he : L = U
    · have hroom : δ * ((m + ((S o).card : ℤ) : ℤ) : ℝ) ≤ L := by
        have hc : (S o).card ≤ jobCap := hcount o
        refine le_trans ?_ ((lt_of_not_ge hsmall).le.trans_eq he.symm)
        apply mul_le_mul_of_nonneg_left _ hδ.le
        exact_mod_cast Int.add_le_add_left (by exact_mod_cast hc) m
      obtain ⟨q, hq, hqs, hqm, hqd, hqsum⟩ :=
        capped_with_all_positive_drops hδ (S o) (w o) (hw o) m (hfloor o) hroom
      exact ⟨q, hq, fun j hj => (hqs j hj).trans (outside j hj), hqm, fun _ => hqd, hqsum⟩
    · obtain ⟨q, hq, hqs, hqm, hqsum⟩ := cap_row hδ (S o) (w o) (hw o) m (hfloor o)
      exact ⟨q, hq, fun j hj => (hqs j hj).trans (outside j hj), hqm,
        fun h => (he h).elim, hqsum.trans (min_eq_right (le_of_not_ge hlo))⟩
  obtain ⟨q, hq, hqOutside, hqMono, hqDrop, hqSum⟩ := newRow
  let v' (l : Fin 2) (j : Fin k) := if l = i then d i j else q j
  have hv' (l : Fin 2) (j : Fin k) : a ≤ v' l j ∧ v' l j ≤ b := by
    by_cases hl : l = i <;> simp [v', hl, hd, hq]
  have hvi' : v' i = d i := by funext j; simp [v']
  have hvo' : v' o = q := by funext j; simp [v', ho]
  have newX : rowLoad δ x v' o = C := by rw [rowLoad, hvo']; exact hqSum
  have newX_i : rowLoad δ x v' i = U := by rw [rowLoad, hvi']; rfl
  have new_span : span δ x v' = U := by
    rw [span_two_rows _ _ _ i o cover, newX_i, newX, max_eq_left hCU.le]
  have trueNewX : span δ x (Function.update v' i (t i)) ≤ C := by
    rw [span_two_rows _ _ _ i o cover]
    exact max_le (by simpa [rowLoad] using htrueRow i)
      (by simpa [rowLoad, ho] using newX.le)
  let z := allocOf f δ v'
  have trueNewZ : span δ z (Function.update v' i (t i)) ≤ C :=
    (hop i v' hv' hvi' x).trans trueNewX
  have newOppZ : rowLoad δ z v' o ≤ C := by
    rw [span_two_rows _ _ _ i o cover] at trueNewZ
    have h := (le_max_right _ _).trans trueNewZ
    simpa [rowLoad, ho] using h
  let T := Finset.univ.filter (fun j => z j = o)
  let A := roundUp δ a
  let B := roundUp δ b
  let gained := ∑ _j ∈ T \ S o, B
  let lost := ∑ j ∈ S o \ T, roundUp δ (w o j)
  let newLost := ∑ j ∈ S o \ T, roundUp δ (q j)
  have hgo : (∑ j ∈ T \ S o, roundUp δ (w o j)) = gained := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show w o j = b by simp [w, (Finset.mem_sdiff.1 hj).2, ho]]
  have hgn : (∑ j ∈ T \ S o, roundUp δ (q j)) = gained := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hqOutside j (Finset.mem_sdiff.1 hj).2]
  have oldDiff : rowLoad δ z w o - L = gained - lost := by
    exact (sums_difference (S o) T (fun j => roundUp δ (w o j))).trans
      (congrArg (fun u => u - lost) hgo)
  have newDiff : rowLoad δ z v' o - C = gained - newLost := by
    rw [rowLoad, hvo', ← hqSum]
    exact (sums_difference (S o) T (fun j => roundUp δ (q j))).trans
      (congrArg (fun u => u - newLost) hgn)
  have hMove : gained ≤ newLost := by linarith [newOppZ, newDiff]
  have hloss : newLost ≤ lost := Finset.sum_le_sum (fun j _ => hqMono j)
  have oldOppZ : rowLoad δ z w o ≤ U := by linarith [oldDiff, hMove, hloss, hLU]
  have ownZF : rowLoad δ z v' i = rowLoad δ z d i := by simp [rowLoad, hvi']
  have ownZW : rowLoad δ z w i = rowLoad δ z d i := by simp [rowLoad, hwi]
  have hZOwn : rowLoad δ z d i ≤ U := by
    have h : span δ z v' ≤ U := ((hf k v' hv').2 x).trans_eq new_span
    rw [span_two_rows _ _ _ i o cover, ownZF] at h
    exact (le_max_left _ _).trans h
  have xStable : z = x := by
    rcases lt_or_eq_of_le hZOwn with hlt | heq
    · exfalso
      have hcrit : U ≤ rowLoad δ z w o := by
        have h : span δ (allocOf f δ w) w ≤ span δ z w := (hf k w hw).2 z
        rw [hxw, hWU, span_two_rows _ _ _ i o cover, ownZW] at h
        exact (le_max_iff.1 h).resolve_left (not_le_of_gt hlt)
      have hLUe : L = U := by linarith [oldDiff, hMove, hloss, hcrit, hLU]
      have hExactLoss : lost = gained := by linarith [oldDiff, oldOppZ, hcrit, hLUe]
      let own (j : Fin k) := roundUp δ (d i j)
      have complement (y : Fin k → Fin 2) :
          Finset.univ \ Finset.univ.filter (fun j => y j = o) =
            Finset.univ.filter (fun j => y j = i) := by
        ext j
        have hh := cover (y j)
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => hh.resolve_right h, fun h e => ho (e.symm.trans h)⟩
      have h1 := Finset.sum_sdiff (f := own) (Finset.subset_univ (S o))
      have h2 := Finset.sum_sdiff (f := own) (Finset.subset_univ T)
      rw [show Finset.univ \ S o = S i from complement x] at h1
      rw [show Finset.univ \ T = Finset.univ.filter (fun j => z j = i) from complement z] at h2
      have hstrict :
          (∑ j ∈ S o \ T, own j) < ∑ j ∈ T \ S o, own j := by
        have h := sums_difference (S o) T own
        change (∑ j ∈ Finset.univ.filter (fun j => z j = i), own j) < ∑ j ∈ S i, own j at hlt
        linarith
      have hFloorGap : (∑ _j ∈ S o \ T, A) < gained :=
        (Finset.sum_le_sum (fun j _ => time_mono hδ (hd i j).1)).trans_lt
          (hstrict.trans_le (Finset.sum_le_sum (fun j _ => time_mono hδ (hd i j).2)))
      have hpos : ∃ j ∈ S o \ T, A < roundUp δ (w o j) := by
        by_contra hnone
        push Not at hnone
        have hh : lost ≤ ∑ _j ∈ S o \ T, A := Finset.sum_le_sum hnone
        linarith [hExactLoss]
      obtain ⟨j, hj, hpos⟩ := hpos
      have hlt' : newLost < lost := Finset.sum_lt_sum (fun u _ => hqMono u)
        ⟨j, hj, hqDrop hLUe j (Finset.mem_sdiff.1 hj).1 hpos⟩
      linarith [hMove, hExactLoss]
    · have zOld : span δ z w = U := by
        rw [span_two_rows _ _ _ i o cover, ownZW, heq, max_eq_left oldOppZ]
      have zNew : span δ z v' = U := by
        rw [span_two_rows _ _ _ i o cover, ownZF, heq, max_eq_left (newOppZ.trans hCU.le)]
      apply hinj
      apply le_antisymm
      · exact hpriority v' hv' x (new_span.trans zNew.symm)
      · have he : span δ z w = span δ (allocOf f δ w) w := by
          rw [hxw, zOld, hWU]
        have h := hpriority w hw z he
        rw [hxw] at h
        exact h
  exact make v' hv' hvi' xStable (newX.le.trans hCC')

theorem solution {k : ℕ} {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin 2 → ℕ) → List (Fin 2)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin 2) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin 2 → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin 2, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin 2 → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i)) :
    let x := allocOf f δ d
    HasAllocationCertificates f δ a b t d
      ((1 + δ / a) * roundedMakespan δ x (corrStar x t)) := by
  classical
  dsimp only
  let x := allocOf f δ d
  let C := span δ x t
  let count (l : Fin 2) := (Finset.univ.filter (fun j => x j = l)).card
  obtain ⟨im, _, hm⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rowLoad δ x t)
  let m : ℤ := ∑ j ∈ Finset.univ.filter (fun j => x j = im), ⌈t im j / δ⌉
  have hC : C = δ * (m : ℝ) := by
    change span δ x t = _
    rw [span_eq, hm]
    simp [m, rowLoad, roundUp, Finset.mul_sum]
  obtain ⟨il, _, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty count
  let q := count il
  have hq (l : Fin 2) : count l ≤ q :=
    (Finset.le_sup' count (Finset.mem_univ l)).trans_eq hl
  have hqC : (q : ℝ) * a ≤ C := by
    have h := Finset.sum_le_sum
      (s := Finset.univ.filter (fun j => x j = il))
      (fun j _ => (ht il j).trans (time_ge (δ := δ) hδ))
    rw [Finset.sum_const, nsmul_eq_mul] at h
    have hh : rowLoad δ x t il ≤ C := by
      dsimp [C]
      rw [span_eq]
      exact Finset.le_sup' _ (Finset.mem_univ il)
    exact h.trans hh
  have hCmul : (q : ℝ) ≤ C / a := (le_div_iff₀ ha).2 hqC
  have hlinear := mul_le_mul_of_nonneg_left hCmul hδ.le
  have hbound : δ * ((m + (q : ℤ) : ℤ) : ℝ) ≤ (1 + δ / a) * C := by
    push_cast
    rw [mul_add, ← hC, add_mul, one_mul, div_mul_eq_mul_div, mul_div_assoc]
    linarith
  have hcert := certificates_at_grid_plus_job_count hab hδ f hf rank hinj hpriority
    t d ht hd hop m q hC.le hq
  intro i hi
  obtain ⟨v, hv, hvi, hxv, y, hy⟩ := hcert i hi
  exact ⟨v, hv, hvi, hxv, y, hy.trans hbound⟩
