-- Prove2me | solution 1 for LongGapsBetweenPrimes.smoothScaleConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:59.145808+00:00
-- url     : https://prove2.me/submissions/50af4693-c4e1-4ff4-b040-892b1166a786

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_smoothEulerConstant_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 0 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]
end LongGapsBetweenPrimes
