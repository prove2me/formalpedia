-- Prove2me | solution 1 for LongGapsBetweenPrimes.coverEta_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:23.592798+00:00
-- url     : https://prove2.me/submissions/0b448594-0668-4007-a1cb-52779b11848a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sieveDelta_pos
import Theorems.Thm_LongGapsBetweenPrimes_coveringConstant_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 0 < coverEta := by
  exact div_pos sieveDelta_pos
    (mul_pos (by norm_num) (add_pos zero_lt_one coveringConstant_pos))
end LongGapsBetweenPrimes
