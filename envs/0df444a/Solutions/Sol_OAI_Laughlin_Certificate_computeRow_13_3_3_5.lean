-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:22.006932+00:00
-- url     : https://prove2.me/submissions/9cd2aae3-24b5-4580-b318-cc553b81181e

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 3 (RowCompute.rows[5]!) =
    (-57497433214015283971815441052326673313590828765154377728000000 : ℤ) := by
  decide +kernel
