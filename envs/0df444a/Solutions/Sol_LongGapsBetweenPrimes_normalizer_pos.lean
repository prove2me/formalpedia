-- Prove2me | solution 1 for LongGapsBetweenPrimes.normalizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:58.720804+00:00
-- url     : https://prove2.me/submissions/eec9027a-df20-4e2c-8a72-7e8e8eba54b2

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_one_lt_of_mem_divisors_erase_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : 1 < P) : 0 < normalizer P := by
  unfold normalizer
  apply Finset.sum_pos
  · intro d hd
    have hd' := one_lt_of_mem_divisors_erase_one hd
    have ht : 0 < (d.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
    exact one_div_pos.mpr (mul_pos ht (Real.log_pos (by exact_mod_cast hd')))
  · exact ⟨P, Finset.mem_erase.mpr ⟨ne_of_gt hP, Nat.mem_divisors_self P (by omega)⟩⟩
end LongGapsBetweenPrimes
