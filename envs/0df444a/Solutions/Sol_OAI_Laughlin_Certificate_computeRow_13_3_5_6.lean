-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:25:11.788977+00:00
-- url     : https://prove2.me/submissions/767d3362-c03d-4580-9219-d5e0fecf8c0a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 5 (RowCompute.rows[6]!) =
    (6544280234333961592039730293921163477965804030654414848000000 : ℤ) := by
  decide +kernel
