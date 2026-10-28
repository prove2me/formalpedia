-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:08.416978+00:00
-- url     : https://prove2.me/submissions/ada06af6-7123-4612-aa84-b1dfd2cc99c7

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 3 (RowCompute.rows[3]!) =
    (655275432593071896846299945949289361163129496384045056000000 : ℤ) := by
  decide +kernel
