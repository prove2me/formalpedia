-- Prove2me | solution 1 for LongGapsBetweenPrimes.smoothEulerConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:27.721687+00:00
-- url     : https://prove2.me/submissions/6e612899-f253-44f3-a1f3-d58916846437

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : 0 < smoothEulerConstant := by
  exact inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))
end LongGapsBetweenPrimes
