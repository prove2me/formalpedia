-- Prove2me | solution 1 for LongGapsBetweenPrimes.coverZ_le_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:26.939256+00:00
-- url     : https://prove2.me/submissions/0d2b047c-ad2b-4e3c-8484-fcdeed96f329

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 0 < x) (hz : coverLogZ x ≤ Real.log x) : coverZ x ≤ ⌊x⌋₊ := by
  exact Nat.floor_mono ((Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hx))
end LongGapsBetweenPrimes
