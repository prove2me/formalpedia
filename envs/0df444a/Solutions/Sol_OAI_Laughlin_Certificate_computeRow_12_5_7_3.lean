-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_5_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:46.676061+00:00
-- url     : https://prove2.me/submissions/b752b404-0c9a-421f-bf0a-5bd941f237ea

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[3]!) =
    (-1832184499366797161703137444355123026022197095997374464000000 : ℤ) := by
  decide +kernel
