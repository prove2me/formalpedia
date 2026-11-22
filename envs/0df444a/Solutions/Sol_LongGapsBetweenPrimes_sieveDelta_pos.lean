-- Prove2me | solution 1 for LongGapsBetweenPrimes.sieveDelta_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:52.093503+00:00
-- url     : https://prove2.me/submissions/8176bba4-455b-4caa-a2c6-e6bdac226665

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_weightConstant_gt_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 0 < sieveDelta := by
  exact one_div_pos.mpr (mul_pos (by norm_num) (zero_lt_one.trans weightConstant_gt_one))
end LongGapsBetweenPrimes
