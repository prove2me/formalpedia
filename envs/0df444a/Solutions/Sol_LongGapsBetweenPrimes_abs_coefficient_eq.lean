-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_coefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:40:10.860776+00:00
-- url     : https://prove2.me/submissions/addd08a1-237e-43bd-a432-98bd82409612

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficient_neg

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P d : ℕ} (hP : 1 < P) (hd : 1 < d) :
    |coefficient P d| = 1 / (normalizer P * Real.log d) := by
  rw [abs_of_neg (coefficient_neg hP hd), coefficient, if_neg (ne_of_gt hd)]
  ring
end LongGapsBetweenPrimes
