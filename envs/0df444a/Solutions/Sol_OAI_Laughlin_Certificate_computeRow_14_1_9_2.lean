-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:31:54.706341+00:00
-- url     : https://prove2.me/submissions/c46c69a2-e1e6-4277-858b-81990e94ddf8

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 9 (RowCompute.rows[2]!) =
    (3384696700144159761566553058759412672578961334250109927424000000 : ℤ) := by
  decide +kernel
