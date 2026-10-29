-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:38.539412+00:00
-- url     : https://prove2.me/submissions/792aae34-39dd-4a5b-8ea8-38f821a253cd

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 9 (RowCompute.rows[4]!) =
    (-31292257728512656217912315520294706230038908266589716480000000 : ℤ) := by
  decide +kernel
