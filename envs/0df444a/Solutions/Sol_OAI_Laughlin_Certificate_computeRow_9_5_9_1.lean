-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:28.784435+00:00
-- url     : https://prove2.me/submissions/101b0d3d-af56-44c4-a7f9-233c8c4f3673

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[1]!) =
    (1517218803322976759301907603209379394622391708633006080000 : ℤ) := by
  decide +kernel
