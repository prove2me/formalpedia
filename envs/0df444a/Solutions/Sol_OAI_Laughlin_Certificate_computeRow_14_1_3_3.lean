-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:16.42996+00:00
-- url     : https://prove2.me/submissions/702f713f-2dac-4a7d-bcd4-1e845e9e45cb

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 3 (RowCompute.rows[3]!) =
    (1282245170712800494014119706353131880934980609608066793472000000 : ℤ) := by
  decide +kernel
