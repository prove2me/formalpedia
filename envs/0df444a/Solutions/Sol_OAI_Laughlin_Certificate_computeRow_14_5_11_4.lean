-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_11_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:56.260265+00:00
-- url     : https://prove2.me/submissions/1a7a9db4-97fc-45c9-ada5-ff886111b949

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 11 (RowCompute.rows[4]!) =
    (87143830597834921762747283406400164257691433092998234112000000 : ℤ) := by
  decide +kernel
