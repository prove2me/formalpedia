-- Prove2me | solution 1 for LongGapsBetweenPrimes.weightConstant_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:59.960875+00:00
-- url     : https://prove2.me/submissions/6ab9e953-c2a3-435b-88d6-1854f1695a0a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_absoluteMomentBound_pos
import Theorems.Thm_LongGapsBetweenPrimes_coefficientControl_pos
import Theorems.Thm_LongGapsBetweenPrimes_normalizerLower_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 1 < weightConstant := by
  unfold weightConstant
  linarith [absoluteMomentBound_pos normalizerLower_pos,
    coefficientControl_pos normalizerLower_pos]
end LongGapsBetweenPrimes
