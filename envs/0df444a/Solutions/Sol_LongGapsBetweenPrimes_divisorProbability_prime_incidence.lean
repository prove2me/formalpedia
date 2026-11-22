-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorProbability_prime_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:48.574384+00:00
-- url     : https://prove2.me/submissions/bb6db975-accc-4b93-b022-e9efbe666e4d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisorIndex
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_prime_incidence

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P p : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hp : p.Prime) (hpP : p ∣ P) :
    (∑ d : DivisorIndex P, divisorProbability P d * if p ∣ d.val then 1 else 0) ≤ 4 / (p : ℝ) := by
  classical
  have hP : P ≠ 0 := h.squarefree.ne_zero
  have hA : 1 ≤ coefficientMoment P 0 := coefficientMoment_ge_one hP 0
  simp only [divisorProbability]
  rw [sum_divisorIndex P (fun d =>
    (coefficient P d ^ 2 / d.totient) / coefficientMoment P 0 *
      if p ∣ d then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (fun d => p ∣ d),
        |coefficient P d| / d.totient := by
      apply Finset.sum_le_sum
      intro d hd
      have hc := h.abs_le_one d (Finset.mem_filter.mp hd).1
      have hs : coefficient P d ^ 2 ≤ |coefficient P d| := by
        nlinarith [sq_abs (coefficient P d), abs_nonneg (coefficient P d)]
      exact (div_le_self
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hA).trans
        (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _))
    _ ≤ 4 / (p : ℝ) := coefficient_prime_incidence h.one_lt h.squarefree hp hpP
      (h.abs_le_one p (Nat.mem_divisors.mpr ⟨hpP, hP⟩))
end LongGapsBetweenPrimes
