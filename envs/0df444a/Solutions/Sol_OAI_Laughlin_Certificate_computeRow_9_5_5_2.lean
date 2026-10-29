-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_9_5_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:14.835679+00:00
-- url     : https://prove2.me/submissions/36373f58-8006-4f40-8354-8efb068ca7a8

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[2]!) =
    (173822138490013131238078506366293139918082652326644940800000 : ℤ) := by
  decide +kernel
