-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_7_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:55.46167+00:00
-- url     : https://prove2.me/submissions/ecca5ec0-c3c3-42e8-a99d-d5e60d18f241

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[5]!) =
    (-647874257176920312223619286133457609151196782513251942400000 : ℤ) := by
  decide +kernel
