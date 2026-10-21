-- Prove2me | solution 1 for HiringLP.ProbeTopK.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:03:46.936854+00:00
-- url     : https://prove2.me/submissions/8ac05173-83d4-4edb-8c29-4d669ebe7842

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

set_option autoImplicit false
open HiringLP.ProbeTopK Finset

lemma HPT_qcoin {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) (i : Fin n) (j : Fin J) :
    I.q i j * coin I x y i j = x i j / y i := by
  obtain ⟨h1, -, -, h0, hy⟩ := hfeas
  by_cases hyi : y i = 0
  · have : x i j = 0 := by
      have := h1 i j
      rw [hyi] at this
      linarith [h0 i j]
    simp [coin, hyi, this]
  · by_cases hq : I.q i j = 0
    · have := h1 i j
      rw [hq] at this
      have hx : x i j = 0 := by linarith [h0 i j, this, mul_zero (y i)]
      simp [coin, hq, hx]
    · have : y i * I.q i j ≠ 0 := mul_ne_zero hyi hq
      simp only [coin, this, if_false]
      field_simp

lemma HPT_pbar {n J : ℕ} (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    pbar x y i = (∑ j, x i j) / y i := by
  by_cases hyi : y i = 0 <;> simp [pbar, hyi]

lemma HPT_B {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) (i : Fin n) :
    ∑ j, I.q i j * coin I x y i j = pbar x y i := by
  rw [HPT_pbar, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => HPT_qcoin I x y hfeas i j

lemma HPT_A {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) (i : Fin n) :
    ∑ j, I.q i j * coin I x y i j * I.r j = vbar I x i * pbar x y i := by
  have hq : ∀ j, I.q i j * coin I x y i j * I.r j = x i j * I.r j / y i := fun j => by
    rw [HPT_qcoin I x y hfeas i j]; ring
  simp_rw [hq]
  rw [← Finset.sum_div, HPT_pbar]
  by_cases hX : ∑ j, x i j = 0
  · have hz : ∀ j, x i j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hfeas.2.2.2.1 i j)).1 hX j (mem_univ _)
    simp [vbar, hX, hz]
  · simp only [vbar, hX, if_false]
    have : ∑ j, x i j * I.r j = ∑ j, I.r j * x i j := sum_congr rfl fun j _ => mul_comm _ _
    rw [this, div_mul_div_comm, mul_comm (∑ j, I.r j * x i j) (∑ j, x i j),
      mul_div_mul_left _ _ hX]

lemma HPT_key {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y)
    (C : Finset (Fin n)) (i0 : Fin n) (hi0 : i0 ∈ C) :
    ∑ V : Fin n → Fin J, (∏ i, I.q i (V i)) *
        (∏ i, if i ∈ C then coin I x y i (V i) else 1 - coin I x y i (V i)) * I.r (V i0) =
      (∏ i, if i ∈ C then pbar x y i else 1 - pbar x y i) * vbar I x i0 := by
  have h1 : ∀ V : Fin n → Fin J, (∏ i, I.q i (V i)) *
        (∏ i, if i ∈ C then coin I x y i (V i) else 1 - coin I x y i (V i)) * I.r (V i0) =
      ∏ i, (I.q i (V i) * (if i ∈ C then coin I x y i (V i) else 1 - coin I x y i (V i)) *
        (if i = i0 then I.r (V i) else 1)) := by
    intro V
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' (univ : Finset (Fin n)) i0
      (fun i => I.r (V i)), if_pos (mem_univ _)]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (j : Fin J) => I.q i j *
    (if i ∈ C then coin I x y i j else 1 - coin I x y i j) * (if i = i0 then I.r j else 1))]
  have h2 : ∀ i, ∑ j, I.q i j * (if i ∈ C then coin I x y i j else 1 - coin I x y i j) *
        (if i = i0 then I.r j else 1) =
      (if i ∈ C then pbar x y i else 1 - pbar x y i) * (if i = i0 then vbar I x i0 else 1) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [if_pos hi0, if_true]
      rw [HPT_A I x y hfeas i, mul_comm]
    · simp only [if_neg hi, mul_one]
      by_cases hc : i ∈ C
      · simp only [if_pos hc]; exact HPT_B I x y hfeas i
      · simp only [if_neg hc]
        have : ∑ j, I.q i j * (1 - coin I x y i j) = 1 - pbar x y i := by
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib, hI.2.2.2.2.2 i, HPT_B I x y hfeas i]
        exact this
  rw [Finset.prod_congr rfl fun i _ => h2 i, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' (univ : Finset (Fin n)) i0 (fun _ => vbar I x i0), if_pos (mem_univ _)]

theorem solution {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) (ord : Equiv.Perm (Fin n)) :
    algReward I x y ord = cutValue I x y ord (DR y) := by
  have hfeas : LPFeasible I x y := hext.1
  unfold algReward cutValue
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hB : i ∈ S ∧ i ∈ C ∧ (univ.filter fun l => l ∈ S ∧ l ∈ C ∧ before ord l i).card < I.k
  · simp only [if_pos hB]
    rw [← HPT_key I hI x y hfeas C i hB.2.1]
  · simp [hB]
