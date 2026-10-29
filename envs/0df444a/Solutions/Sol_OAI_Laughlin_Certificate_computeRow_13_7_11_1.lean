-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_11_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:23.10119+00:00
-- url     : https://prove2.me/submissions/2ebf59e5-4632-4a3a-aa92-1338a874e4ee

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 11 (RowCompute.rows[1]!) =
    (-637010100716664439760506138358233613456779400573878272000000 : ℤ) := by
  decide +kernel
