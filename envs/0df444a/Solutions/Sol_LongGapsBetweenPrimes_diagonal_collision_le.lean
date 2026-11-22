-- Prove2me | solution 1 for LongGapsBetweenPrimes.diagonal_collision_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:18.0158+00:00
-- url     : https://prove2.me/submissions/1c0f3dfd-2ed4-4ef3-a53d-c8d23452980c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one
import Theorems.Thm_LongGapsBetweenPrimes_product_collision_bound
import Theorems.Thm_LongGapsBetweenPrimes_divisorProbability_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisorProbability
import Theorems.Thm_LongGapsBetweenPrimes_tupleMass_eq_probability
import Theorems.Thm_LongGapsBetweenPrimes_divisorProbability_prime_incidence
import Theorems.Thm_LongGapsBetweenPrimes_noncoprime_pair_iff_common_prime

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P M k : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (∑ r : DivisorTuple P k, tupleMass r *
      if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0) ≤
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by
  classical
  have hP : P ≠ 0 := h.squarefree.ne_zero
  have hA : 0 ≤ coefficientMoment P 0 ^ k :=
    pow_nonneg (zero_le_one.trans (coefficientMoment_ge_one hP 0)) k
  have hcollision := product_collision_bound (divisorProbability P)
    (divisorProbability_nonneg hP) (sum_divisorProbability hP)
    (fun (p : P.primeFactors) (d : DivisorIndex P) => p.val ∣ d.val) k
  have hincidence :
      (∑ p : P.primeFactors,
        (∑ d : DivisorIndex P, divisorProbability P d *
          if p.val ∣ d.val then 1 else 0) ^ 2) ≤ 16 / (M : ℝ) := by
    calc
      _ ≤ ∑ p : P.primeFactors, (4 / (p.val : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro p _
        have hnonneg : 0 ≤ ∑ d : DivisorIndex P, divisorProbability P d *
            if p.val ∣ d.val then 1 else 0 := by
          apply Finset.sum_nonneg
          intro d _
          exact mul_nonneg (divisorProbability_nonneg hP d) (by split_ifs <;> norm_num)
        exact pow_le_pow_left₀ hnonneg
          (divisorProbability_prime_incidence h
            (Nat.prime_of_mem_primeFactors p.property)
            (Nat.dvd_of_mem_primeFactors p.property)) 2
      _ = 16 * ∑ p ∈ P.primeFactors, 1 / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        change (∑ p ∈ P.primeFactors.attach, (4 / (p.val : ℝ)) ^ 2) = _
        rw [Finset.sum_attach P.primeFactors (fun p : ℕ => (4 / (p : ℝ)) ^ 2)]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 16 * (1 / (M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          _ ≤ ∑ p ∈ Finset.Ioc M (max M P), 1 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun p hp => Finset.mem_Ioc.mpr ⟨hmin p hp,
                (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) (Nat.dvd_of_mem_primeFactors hp)).trans
                  (le_max_right _ _)⟩) (fun _ _ _ => by positivity)
          _ ≤ 1 / (M : ℝ) - 1 / ((max M P : ℕ) : ℝ) := by
            simpa only [one_div] using
              (sum_Ioc_inv_sq_le_sub (α := ℝ) hM.ne' (le_max_left M P))
          _ ≤ _ := sub_le_self _ (by positivity)
      _ = 16 / (M : ℝ) := by ring
  calc
    _ = coefficientMoment P 0 ^ k *
        ∑ r : DivisorTuple P k, (∏ i, divisorProbability P (r i)) *
          if ∃ p : P.primeFactors, ∃ i j,
            i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val then 1 else 0 := by
      simp_rw [tupleMass_eq_probability hP, noncoprime_pair_iff_common_prime hP,
        mul_assoc]
      rw [Finset.mul_sum]
    _ ≤ coefficientMoment P 0 ^ k * ((k : ℝ) ^ 2 * (16 / (M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact hcollision.trans (mul_le_mul_of_nonneg_left hincidence (sq_nonneg _))
    _ = _ := by ring
end LongGapsBetweenPrimes
