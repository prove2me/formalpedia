-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:44.015744+00:00
-- url     : https://prove2.me/submissions/a56ae3f3-b476-4984-baf6-bfb13d7c5d37

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 11 (RowCompute.rows[3]!) =
    (-577321510991864292272120272923034279590016034808306597888000000 : ℤ) := by
  decide +kernel
