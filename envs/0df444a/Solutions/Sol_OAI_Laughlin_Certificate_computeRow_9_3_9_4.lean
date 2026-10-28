-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_3_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:31.611551+00:00
-- url     : https://prove2.me/submissions/e1adf7f6-9fb6-4c08-a73c-7b2f4ffeb902

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[4]!) =
    (-105466825227046141787298456174023648883618159889534156800000 : ℤ) := by
  decide +kernel
