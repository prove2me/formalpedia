-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_7_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:27:34.596976+00:00
-- url     : https://prove2.me/submissions/f837bc1f-643a-4e97-bf9a-f430f8924478

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 7 11 (RowCompute.rows[5]!) =
    (657261822139230743266100447099308105567842424294735872000000 : ℤ) := by
  decide +kernel
