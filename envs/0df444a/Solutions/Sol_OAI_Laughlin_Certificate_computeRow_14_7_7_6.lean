-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:39:53.331798+00:00
-- url     : https://prove2.me/submissions/dc63bd12-a59f-4ebc-a38a-bf2082935c3a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 7 (RowCompute.rows[6]!) =
    (-29813118346845196622624036130499543939931627223836000256000000 : ℤ) := by
  decide +kernel
