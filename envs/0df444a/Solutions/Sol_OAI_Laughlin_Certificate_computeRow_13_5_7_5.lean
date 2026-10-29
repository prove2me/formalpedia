-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:37:30.52893+00:00
-- url     : https://prove2.me/submissions/f0a02e9a-85c4-4c89-9c09-aaf7ef73ca13

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 7 (RowCompute.rows[5]!) =
    (21322312780608858700576231366363396956885416234572578816000000 : ℤ) := by
  decide +kernel
