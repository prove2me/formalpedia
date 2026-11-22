-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_coefficient_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:40.345507+00:00
-- url     : https://prove2.me/submissions/b36e7f7d-6b62-44a0-9204-9d994783034d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_neg

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P p e : ℕ} (hP : 1 < P) (hp : 1 ≤ p) (he : 1 < e) :
    |coefficient P (p * e)| ≤ |coefficient P e| := by
  have hpe : e ≤ p * e := by simpa using Nat.mul_le_mul_right e hp
  have hpe1 : 1 < p * e := he.trans_le hpe
  rw [abs_of_neg (coefficient_neg hP hpe1), abs_of_neg (coefficient_neg hP he)]
  simp only [coefficient, if_neg (ne_of_gt hpe1), if_neg (ne_of_gt he),
    neg_div, neg_neg]
  apply one_div_le_one_div_of_le
  · exact mul_pos (normalizer_pos hP) (Real.log_pos (by exact_mod_cast he))
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans he))
        (by exact_mod_cast hpe)) (normalizer_pos hP).le
end LongGapsBetweenPrimes
