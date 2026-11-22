-- Prove2me | solution 1 for LongGapsBetweenPrimes.coverEta_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:02.351738+00:00
-- url     : https://prove2.me/submissions/23e9e71b-0e88-4b24-ae99-4218c82978cc

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sieveDelta_lt_half
import Theorems.Thm_LongGapsBetweenPrimes_coveringConstant_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : coverEta ≤ 1 := by
  unfold coverEta
  apply (div_le_one (by linarith [coveringConstant_pos])).mpr
  linarith [sieveDelta_lt_half, coveringConstant_pos]
end LongGapsBetweenPrimes
