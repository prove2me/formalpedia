-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:33:08.222309+00:00
-- url     : https://prove2.me/submissions/8ce48cdc-2fac-4c00-891e-f44f92503e78

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 5 (RowCompute.rows[1]!) =
    (887627653790877294587671801762105566930130713540820992000000 : ℤ) := by
  decide +kernel
