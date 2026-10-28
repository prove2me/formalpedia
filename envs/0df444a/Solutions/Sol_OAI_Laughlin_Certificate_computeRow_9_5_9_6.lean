-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:05.749394+00:00
-- url     : https://prove2.me/submissions/22c72ce0-44f6-4666-bcd4-a66b6ebf0b5b

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[6]!) =
    (-7065304641313883158404581656472081546480859568983244800000 : ℤ) := by
  decide +kernel
