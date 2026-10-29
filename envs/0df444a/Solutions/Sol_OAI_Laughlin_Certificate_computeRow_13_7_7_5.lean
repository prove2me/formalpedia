-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:48:15.217116+00:00
-- url     : https://prove2.me/submissions/9ef5a505-74ac-491d-afed-32bc61bebc9e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 7 (RowCompute.rows[5]!) =
    (-26923938800508290435209014658938202159100453459545030656000000 : ℤ) := by
  decide +kernel
