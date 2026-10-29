-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:15.463114+00:00
-- url     : https://prove2.me/submissions/7b570f95-c756-45ed-9261-e7f4527dee03

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 9 (RowCompute.rows[2]!) =
    (409389821307827549661009698714149269465157086915952902144000000 : ℤ) := by
  decide +kernel
