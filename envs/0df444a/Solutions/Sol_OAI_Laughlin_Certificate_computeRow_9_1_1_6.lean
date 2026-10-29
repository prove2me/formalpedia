-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_1_1_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:47.247688+00:00
-- url     : https://prove2.me/submissions/4020b97b-5835-4830-b3e9-944d6704ca41

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[6]!) =
    (-47335064343067846647978682808120256786731536109430374400000 : ℤ) := by
  decide +kernel
