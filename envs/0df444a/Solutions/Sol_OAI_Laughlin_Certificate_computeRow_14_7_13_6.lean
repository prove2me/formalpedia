-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_13_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:09.715852+00:00
-- url     : https://prove2.me/submissions/d8249497-aa10-43e6-95a7-d8079e49c916

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 13 (RowCompute.rows[6]!) =
    (39069141911891416285529850616879424218758223829152038912000000 : ℤ) := by
  decide +kernel
