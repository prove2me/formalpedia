-- Prove2me | solution 1 for LongGapsBetweenPrimes.sieveDelta_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:52.497727+00:00
-- url     : https://prove2.me/submissions/ac819cac-bc53-45ff-a4d8-4efd6eb7aa01

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_weightConstant_gt_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : sieveDelta < 1 / 2 := by
  unfold sieveDelta
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith [weightConstant_gt_one]
end LongGapsBetweenPrimes
