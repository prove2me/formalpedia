-- Prove2me | solution 1 for Hermite1DimdLEAN.shellCountingFormula
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:10:55.182821+00:00
-- url     : https://prove2.me/submissions/ee7fd29b-b704-4458-9ba5-522519cd5453

import Mathlib


theorem solution (d r : ℕ) :
    (2 * r + 1) ^ d - (2 * r - 1) ^ d ≤ (2 * r + 1) ^ d := by
  exact Nat.sub_le _ _
