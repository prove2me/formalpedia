-- Prove2me | solution 1 for LongGapsBetweenPrimes.coveringConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:22.122479+00:00
-- url     : https://prove2.me/submissions/6ad2fbe9-79ff-4a13-8cd0-fea31904f514

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_smoothScaleConstant_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 0 < coveringConstant := by
  have := smoothScaleConstant_pos
  unfold coveringConstant
  positivity
end LongGapsBetweenPrimes
