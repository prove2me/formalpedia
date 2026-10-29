-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_11_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:27.777689+00:00
-- url     : https://prove2.me/submissions/383dc25d-36d1-4f70-9a8b-85641bbbdae4

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 11 (RowCompute.rows[1]!) =
    (-812092576980514866926686630021820842414854657384067891200000 : ℤ) := by
  decide +kernel
