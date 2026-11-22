-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliary_coefficient_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:33.442743+00:00
-- url     : https://prove2.me/submissions/651ff1f0-f62a-4c07-801e-e5f6b1385d1b

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos
import Theorems.Thm_LongGapsBetweenPrimes_abs_coefficient_eq
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_divisor_gt

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hP : 1 < auxiliaryProduct Z Y)
    (hZ : 1 < Z) (hB : 1 ≤ normalizer (auxiliaryProduct Z Y) * Real.log Z)
    {d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors) :
    |coefficient (auxiliaryProduct Z Y) d| ≤ 1 := by
  by_cases hd1 : d = 1
  · simp [hd1, coefficient]
  have hZd := auxiliary_divisor_gt (Finset.mem_erase.mpr ⟨hd1, hd⟩)
  rw [abs_coefficient_eq hP (hZ.trans hZd)]
  have hden : 1 ≤ normalizer (auxiliaryProduct Z Y) * Real.log d :=
    hB.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans hZ))
        (by exact_mod_cast hZd.le)) (normalizer_pos hP).le)
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
end LongGapsBetweenPrimes
