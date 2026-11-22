-- Prove2me | solution 1 for LongGapsBetweenPrimes.smoothScaleConstant_gt_ten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:10.846186+00:00
-- url     : https://prove2.me/submissions/366ff80e-cf5e-4f5c-aba9-9282835f0d8c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_smoothEulerConstant_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 10 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]
end LongGapsBetweenPrimes
