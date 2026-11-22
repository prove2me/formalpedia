-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientRemainder_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:51.503595+00:00
-- url     : https://prove2.me/submissions/4b13a182-6e4f-4050-8b80-591e41ae3c30

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_partial_cancellation_nonneg

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P m : ℕ} (hP : 1 < P) (hm : 0 < m)
    {D : ℝ} (hcut : (m : ℝ) ≤ D) : 0 ≤ coefficientRemainder P m D := by
  apply partial_cancellation_nonneg hP _ (Finset.filter_subset _ _)
  refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), ?_, by simp⟩
  exact (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by simpa using hcut)
end LongGapsBetweenPrimes
