-- Prove2me | solution 1 for NConjecture.bb94_lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T09:17:58.484977+00:00
-- url     : https://prove2.me/submissions/bd46e913-4433-4f8e-ba50-8feecd6e07fd

import Mathlib
namespace NConjecture

open Polynomial

noncomputable def AuxBB_TV : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1, 2)
  | k + 1 => (X * (AuxBB_TV k).1 + (AuxBB_TV k).1 + (AuxBB_TV k).2, X * (AuxBB_TV k).1 + (AuxBB_TV k).2)

noncomputable def AuxBB_H (k : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (k + 1), C (f.coeff j) * X ^ (k - j) * (X - 1) ^ (2 * j)

theorem AuxBB_cx (p : Polynomial ℤ) (j : ℕ) : (X * p).coeff j = if j = 0 then 0 else p.coeff (j - 1) := by
  cases j with
  | zero => simp
  | succ j => simp [coeff_X_mul]

theorem AuxBB_inv (k : ℕ) :
    (∀ j, k < j → (AuxBB_TV k).1.coeff j = 0) ∧ (∀ j, k < j → (AuxBB_TV k).2.coeff j = 0) ∧
    (∀ j ≤ k, 0 < (AuxBB_TV k).1.coeff j) ∧ (∀ j, 0 ≤ (AuxBB_TV k).1.coeff j) ∧
    (∀ j, 0 ≤ (AuxBB_TV k).2.coeff j) := by
  induction k with
  | zero =>
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun j => ?_⟩
    · simp only [AuxBB_TV, coeff_one]; rw [if_neg (by omega)]
    · simp only [AuxBB_TV]
      rw [show (2 : Polynomial ℤ) = C 2 by simp, coeff_C, if_neg (by omega)]
    · simp only [AuxBB_TV, coeff_one]; rw [if_pos (by omega)]; norm_num
    · simp only [AuxBB_TV, coeff_one]; split_ifs <;> norm_num
    · simp only [AuxBB_TV]
      rw [show (2 : Polynomial ℤ) = C 2 by simp, coeff_C]; split_ifs <;> norm_num
  | succ k ih =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun j => ?_⟩
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      rw [if_neg (by omega), a1 (j - 1) (by omega), a1 j (by omega), a2 j (by omega)]; norm_num
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      rw [if_neg (by omega), a1 (j - 1) (by omega), a2 j (by omega)]; norm_num
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      have := a5 j
      split_ifs with h
      · have := a3 j (by omega); linarith
      · rcases Nat.lt_or_ge k j with h' | h'
        · have := a3 (j - 1) (by omega); have := a4 j; linarith
        · have := a3 j h'; have := a4 (j - 1); linarith
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      have := a4 j; have := a5 j; have := a4 (j - 1)
      split_ifs <;> linarith
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      have := a5 j; have := a4 (j - 1)
      split_ifs <;> linarith

theorem AuxBB_Hadd (k : ℕ) (f g : Polynomial ℤ) : AuxBB_H k (f + g) = AuxBB_H k f + AuxBB_H k g := by
  unfold AuxBB_H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coeff_add, C_add]; ring

theorem AuxBB_HX (k : ℕ) (f : Polynomial ℤ) : AuxBB_H (k + 1) (X * f) = (X - 1) ^ 2 * AuxBB_H k f := by
  unfold AuxBB_H
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [coeff_X_mul, coeff_X_mul_zero, C_0, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show k + 1 - (j + 1) = k - j by omega, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  ring

theorem AuxBB_H1 (k : ℕ) (f : Polynomial ℤ) (hf : f.coeff (k + 1) = 0) :
    AuxBB_H (k + 1) f = X * AuxBB_H k f := by
  unfold AuxBB_H
  rw [Finset.sum_range_succ (n := k + 1), hf, C_0, zero_mul, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := Finset.mem_range.mp hj
  rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
  ring

theorem AuxBB_id (k : ℕ) :
    AuxBB_H k (AuxBB_TV k).1 = ∑ i ∈ Finset.range (2 * k + 1), (X : Polynomial ℤ) ^ i ∧
    AuxBB_H k (AuxBB_TV k).2 = X ^ (2 * k) + 1 := by
  induction k with
  | zero =>
    have h2 : (2 : Polynomial ℤ).coeff 0 = 2 := by
      rw [show (2 : Polynomial ℤ) = C 2 by simp, coeff_C_zero]
    refine ⟨by simp [AuxBB_H, AuxBB_TV], ?_⟩
    simp only [AuxBB_H, AuxBB_TV, zero_add, Finset.sum_range_one, h2, Nat.sub_self, pow_zero,
      mul_zero, mul_one]
    rw [show (C 2 : Polynomial ℤ) = 2 by simp]; norm_num
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    obtain ⟨a1, a2, -, -, -⟩ := AuxBB_inv k
    have g := geom_sum_mul (X : Polynomial ℤ) (2 * k + 1)
    have hT := AuxBB_H1 k _ (a1 (k + 1) (by omega))
    have hV := AuxBB_H1 k _ (a2 (k + 1) (by omega))
    simp only [AuxBB_TV]
    rw [AuxBB_Hadd, AuxBB_Hadd, AuxBB_Hadd, AuxBB_HX, hT, hV, i1, i2]
    have e : ∑ i ∈ Finset.range (2 * (k + 1) + 1), (X : Polynomial ℤ) ^ i =
        (∑ i ∈ Finset.range (2 * k + 1), (X : Polynomial ℤ) ^ i) + X ^ (2 * k + 1) + X ^ (2 * k + 2) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring, Finset.sum_range_succ _ (2 * k + 2),
        Finset.sum_range_succ _ (2 * k + 1)]
    constructor
    · rw [e]
      linear_combination X * g
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      linear_combination (X - 1) * g

theorem bb94_lemma_1 (k : ℕ) :
    ∃ f : Polynomial ℤ, f.natDegree = k ∧ (∀ j ≤ k, 0 < f.coeff j) ∧
      (∑ i ∈ Finset.range (2 * k + 1), (Polynomial.X : Polynomial ℤ) ^ i) =
        ∑ j ∈ Finset.range (k + 1),
          Polynomial.C (f.coeff j) * Polynomial.X ^ (k - j) * (Polynomial.X - 1) ^ (2 * j) := by
  obtain ⟨a1, -, a3, -, -⟩ := AuxBB_inv k
  refine ⟨(AuxBB_TV k).1, ?_, a3, ?_⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr a1)
      (ne_of_gt (a3 k le_rfl))
  · exact (AuxBB_id k).1.symm

end NConjecture

theorem solution (k : ℕ) :
    ∃ f : Polynomial ℤ, f.natDegree = k ∧ (∀ j ≤ k, 0 < f.coeff j) ∧
      (∑ i ∈ Finset.range (2 * k + 1), (Polynomial.X : Polynomial ℤ) ^ i) =
        ∑ j ∈ Finset.range (k + 1),
          Polynomial.C (f.coeff j) * Polynomial.X ^ (k - j) * (Polynomial.X - 1) ^ (2 * j) :=
  NConjecture.bb94_lemma_1 k
