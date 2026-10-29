-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_13_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:30.901679+00:00
-- url     : https://prove2.me/submissions/304d722c-3871-4e61-a5ad-86389931a27e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 13 (RowCompute.rows[4]!) =
    (609158292241652863060122920154853713408781452932057923584000000 : ℤ) := by
  decide +kernel
