-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_1_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:59.846068+00:00
-- url     : https://prove2.me/submissions/cbc7ba94-902f-4371-b52c-37c75f913c61

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 1 5 (RowCompute.rows[4]!) =
    (1517818230772684777571117121529191755557410679603624673280000000 : ℤ) := by
  decide +kernel
