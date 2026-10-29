-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_13_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:25.381507+00:00
-- url     : https://prove2.me/submissions/c97a6be8-18c1-4dcb-bbf9-407d45ef311d

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 13 (RowCompute.rows[5]!) =
    (2527368214084064824498765089739065356437821101607688863744000000 : ℤ) := by
  decide +kernel
