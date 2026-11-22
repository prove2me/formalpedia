-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficient_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:27.781876+00:00
-- url     : https://prove2.me/submissions/4eab7445-57a4-4813-a346-6f0fd6227b12

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    coefficient P d < 0 := by
  rw [coefficient, if_neg (ne_of_gt hd)]
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos (normalizer_pos hP) (Real.log_pos (by exact_mod_cast hd)))
end LongGapsBetweenPrimes
