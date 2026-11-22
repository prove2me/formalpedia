-- Prove2me | solution 1 for LongGapsBetweenPrimes.coveringConstant_mul_eta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:26.841534+00:00
-- url     : https://prove2.me/submissions/a92fd75a-4ff0-424b-9917-f0edeca6d157

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sieveDelta_pos
import Theorems.Thm_LongGapsBetweenPrimes_coveringConstant_pos

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : coveringConstant * coverEta ≤ sieveDelta := by
  have hC := coveringConstant_pos
  have hδ := sieveDelta_pos
  unfold coverEta
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hC hδ]
end LongGapsBetweenPrimes
