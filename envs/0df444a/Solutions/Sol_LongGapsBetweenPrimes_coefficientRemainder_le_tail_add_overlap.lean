-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientRemainder_le_tail_add_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:05.518818+00:00
-- url     : https://prove2.me/submissions/169192fb-21b1-4f61-90a1-acc5808cbe65

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_partial_cancellation

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P m : ℕ} (hP : 1 < P)
    (hm : 0 < m) {D : ℝ} (hcut : (m : ℝ) ≤ D) :
    coefficientRemainder P m D ≤
      (∑ d ∈ P.divisors.filter (fun d : ℕ => D / m < (d : ℝ)), |coefficient P d| / d.totient) +
      ∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient := by
  classical
  have h1 : (1 : ℕ) ∈ P.divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ D / m ∧ d.Coprime m) := by
    refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), ?_, by simp⟩
    exact (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by simpa using hcut)
  rw [coefficientRemainder, partial_cancellation hP _ (Finset.filter_subset _ _) h1,
    ← Finset.filter_not]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  have hnonneg : 0 ≤ |coefficient P d| / (d.totient : ℝ) := by positivity
  by_cases hd : (d : ℝ) ≤ D / m <;> by_cases hdm : d.Coprime m <;>
    simp [← not_le, hd, hdm, hnonneg]
end LongGapsBetweenPrimes
