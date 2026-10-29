-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:34:37.382168+00:00
-- url     : https://prove2.me/submissions/2cc8c03a-b707-4927-b3f0-728309f83316

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 9 (RowCompute.rows[4]!) =
    (-44654633011716535933441931844558689436598296813502464000000 : ℤ) := by
  decide +kernel
