-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_3_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:54.585225+00:00
-- url     : https://prove2.me/submissions/256e0d0c-0045-44dc-897b-ed961cef4df6

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 3 11 (RowCompute.rows[5]!) =
    (-59129890095929001930396690967085239185902202075274543104000000 : ℤ) := by
  decide +kernel
