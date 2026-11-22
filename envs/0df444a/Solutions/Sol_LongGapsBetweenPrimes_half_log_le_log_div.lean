-- Prove2me | solution 1 for LongGapsBetweenPrimes.half_log_le_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:38.889707+00:00
-- url     : https://prove2.me/submissions/4d4717ed-15fe-42da-8f2d-fa81697f732b

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {u c : ℝ} (hu : 0 < u) (hc : 0 < c)
    (h : 2 * Real.log c ≤ Real.log u) : Real.log u / 2 ≤ Real.log (u / c) := by
  rw [Real.log_div hu.ne' hc.ne']
  linarith
end LongGapsBetweenPrimes
