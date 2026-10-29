-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:36:23.960404+00:00
-- url     : https://prove2.me/submissions/ac3a8791-1df7-472f-8942-a95c6a92b722

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 3 (RowCompute.rows[5]!) =
    (-1341113216013228497801673126927937048080036493126231130112000000 : ℤ) := by
  decide +kernel
