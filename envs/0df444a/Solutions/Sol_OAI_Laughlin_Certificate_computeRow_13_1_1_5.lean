-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:20.928515+00:00
-- url     : https://prove2.me/submissions/30354258-dadc-4bf6-8034-fe5f13d98478

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 1 (RowCompute.rows[5]!) =
    (-6999368456767841597942223162380465019025026853822657462272000000 : ℤ) := by
  decide +kernel
