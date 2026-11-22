-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficient_sq_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:04.152622+00:00
-- url     : https://prove2.me/submissions/dee5b46c-8ac2-4752-a2c3-be7cd3c1d891

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_neg

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    coefficient P d ^ 2 * Real.log d = |coefficient P d| / normalizer P := by
  rw [abs_of_neg (coefficient_neg hP hd), coefficient, if_neg (ne_of_gt hd)]
  have hB := ne_of_gt (normalizer_pos hP)
  have hlog := ne_of_gt (Real.log_pos (by exact_mod_cast hd : (1 : ℝ) < d))
  field_simp
end LongGapsBetweenPrimes
