-- Prove2me | solution 1 for OAI.PiExponent.InterpolationMatrix.affinePower_coeff_translate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:59:19.487099+00:00
-- url     : https://prove2.me/submissions/6705c225-6dc9-4833-9573-1fd5460dda93

import Mathlib
import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators
open OAI.PiExponent
theorem h41_uni {R : Type*} [CommSemiring R] (n b : ℕ) (z e : R) :
    ∑ a ∈ Finset.range (n + 1), ((a.choose b : ℕ) : R) * e ^ (a - b) *
      (((n.choose a : ℕ) : R) * z ^ (n - a)) = ((n.choose b : ℕ) : R) * (z + e) ^ (n - b) := by
  by_cases hbn : n < b
  · rw [Nat.choose_eq_zero_of_lt hbn]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro a ha
    have : a < b := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hbn
    simp [Nat.choose_eq_zero_of_lt this]
  push Not at hbn
  have hsplit : n + 1 = b + (n - b + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h0 : ∑ a ∈ Finset.range b, ((a.choose b : ℕ) : R) * e ^ (a - b) *
      (((n.choose a : ℕ) : R) * z ^ (n - a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp ha)]
  rw [h0, zero_add, add_comm z e, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : b + j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hc := @Nat.choose_mul n (b + j) b (Nat.le_add_right b j)
  rw [Nat.add_sub_cancel_left] at hc
  have hc' : ((n.choose (b + j) : ℕ) : R) * (((b + j).choose b : ℕ) : R) =
      ((n.choose b : ℕ) : R) * (((n - b).choose j : ℕ) : R) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hc]
  have he : n - (b + j) = n - b - j := by omega
  rw [Nat.add_sub_cancel_left, he]
  calc _ = (((n.choose (b + j) : ℕ) : R) * (((b + j).choose b : ℕ) : R)) * (e ^ j * z ^ (n - b - j)) := by ring
    _ = (((n.choose b : ℕ) : R) * (((n - b).choose j : ℕ) : R)) * (e ^ j * z ^ (n - b - j)) := by rw [hc']
    _ = _ := by ring

theorem h41_expand {R : Type*} [CommSemiring R] {m : ℕ} (c : Fin m → R) (n : Fin m → ℕ) :
    (∏ i, (MvPolynomial.C (c i) + MvPolynomial.X i) ^ n i : MvPolynomial (Fin m) R) =
      ∑ k ∈ Fintype.piFinset (fun i => Finset.range (n i + 1)),
        MvPolynomial.monomial (InterpolationMatrix.exponentVector k)
          (∏ i, ((n i).choose (k i) : R) * c i ^ (n i - k i)) := by
  classical
  have h1 : ∀ i, (MvPolynomial.C (c i) + MvPolynomial.X i : MvPolynomial (Fin m) R) ^ n i =
      ∑ k ∈ Finset.range (n i + 1),
        MvPolynomial.C (((n i).choose k : R) * c i ^ (n i - k)) * MvPolynomial.X i ^ k := by
    intro i
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    simp only [map_mul, map_pow, map_natCast]
    ring
  simp_rw [h1]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [MvPolynomial.monomial_eq, Finset.prod_mul_distrib, ← map_prod]
  congr 1
  simp only [InterpolationMatrix.exponentVector]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i; simp

theorem h41_coeff {R : Type*} [CommSemiring R] {m : ℕ} (c : Fin m → R) (n a : Fin m → ℕ) :
    (∏ i, (MvPolynomial.C (c i) + MvPolynomial.X i) ^ n i : MvPolynomial (Fin m) R).coeff
      (InterpolationMatrix.exponentVector a) = ∏ i, ((n i).choose (a i) : R) * c i ^ (n i - a i) := by
  classical
  rw [h41_expand, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  have hinj : ∀ k, InterpolationMatrix.exponentVector k = InterpolationMatrix.exponentVector a ↔ k = a := by
    intro k
    simp [InterpolationMatrix.exponentVector]
  simp only [hinj]
  rw [Finset.sum_ite_eq']
  split_ifs with ha
  · rfl
  · rw [Fintype.mem_piFinset] at ha
    push Not at ha
    obtain ⟨i, hi⟩ := ha
    have : n i < a i := by have := Finset.mem_range.not.mp hi; omega
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt this]

theorem solution
    {R : Type*} [CommSemiring R] {m : ℕ}
    (f : R) (z e : Fin m → R) (n b : Fin m → ℕ)
    (S : Finset (Fin m → ℕ))
    (hS : ∀ a : Fin m → ℕ, (∀ i, a i ≤ n i) → a ∈ S) :
    (MvPolynomial.C f *
      ∏ i, (MvPolynomial.C (z i + e i) + MvPolynomial.X i) ^ n i).coeff
        (InterpolationMatrix.exponentVector b) =
      ∑ a : ↥S,
        ((∏ i, (a.1 i).choose (b i) : ℕ) : R) *
          (∏ i, e i ^ (a.1 i - b i)) *
          (MvPolynomial.C f *
            ∏ i, (MvPolynomial.C (z i) + MvPolynomial.X i) ^ n i).coeff
              (InterpolationMatrix.exponentVector a.1) := by
  classical
  rw [MvPolynomial.coeff_C_mul, h41_coeff]
  simp_rw [MvPolynomial.coeff_C_mul, h41_coeff]
  rw [Finset.sum_coe_sort S (fun a => ((∏ i, (a i).choose (b i) : ℕ) : R) * (∏ i, e i ^ (a i - b i)) *
      (f * ∏ i, ((n i).choose (a i) : R) * z i ^ (n i - a i)))]
  have hsub : Fintype.piFinset (fun i => Finset.range (n i + 1)) ⊆ S := by
    intro a ha
    rw [Fintype.mem_piFinset] at ha
    exact hS a (fun i => Nat.lt_succ_iff.mp (Finset.mem_range.mp (ha i)))
  rw [← Finset.sum_subset hsub]
  · have : ∀ a : Fin m → ℕ, ((∏ i, (a i).choose (b i) : ℕ) : R) * (∏ i, e i ^ (a i - b i)) *
        (f * ∏ i, ((n i).choose (a i) : R) * z i ^ (n i - a i)) =
        f * ∏ i, (((a i).choose (b i) : ℕ) : R) * e i ^ (a i - b i) *
          (((n i).choose (a i) : ℕ) : R) * z i ^ (n i - a i) := by
      intro a
      rw [Nat.cast_prod]
      simp only [Finset.prod_mul_distrib]
      ring
    simp_rw [this]
    rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun i => Finset.range (n i + 1))
      (fun i k => ((k.choose (b i) : ℕ) : R) * e i ^ (k - b i) * ((n i).choose k : ℕ) * z i ^ (n i - k))]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← h41_uni]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro a _ ha
    rw [Fintype.mem_piFinset] at ha
    push Not at ha
    obtain ⟨i, hi⟩ := ha
    have : n i < a i := by have := Finset.mem_range.not.mp hi; omega
    have hz : ∏ i, ((n i).choose (a i) : R) * z i ^ (n i - a i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt this])
    rw [hz]; simp

