-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_primeFactors_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:22.269817+00:00
-- url     : https://prove2.me/submissions/0aba8837-d504-4bf1-80f0-c7706ce0f4ea

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P m : ℕ} (hP : Squarefree P) (hm : m ∣ P)
    {M : ℝ} (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    (∑ p ∈ m.primeFactors, 4 / (p : ℝ)) ≤ 4 * Real.log m / (M * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
    calc
      _ = ∑ p ∈ m.primeFactors, Real.log 2 := by simp
      _ ≤ ∑ p ∈ m.primeFactors, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by norm_num)
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
      _ = Real.log m := by
        rw [← Real.log_prod (fun p hp =>
          Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero),
          ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hm)]
  calc
    _ ≤ ∑ p ∈ m.primeFactors, 4 / M := by
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_left (by norm_num) hM
      exact hmin p ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
        ((Nat.dvd_of_mem_primeFactors hp).trans hm) hP.ne_zero)
    _ = (4 / M) * (m.primeFactors.card : ℝ) := by simp [mul_comm]
    _ ≤ (4 / M) * (Real.log m / Real.log 2) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hlog2).mpr hcard) (by positivity)
    _ = _ := by ring
end LongGapsBetweenPrimes
