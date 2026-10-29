-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:25.556878+00:00
-- url     : https://prove2.me/submissions/5665880f-70b5-47d0-8a58-d9211072352b

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 9 (RowCompute.rows[2]!) =
    (91307293309090509794891980040727999151086096008356036608000000 : ℤ) := by
  decide +kernel
