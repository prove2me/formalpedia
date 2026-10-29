-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_14_11_11_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:52:38.412651+00:00
-- url     : https://prove2.me/submissions/7ab98a75-f44c-4963-807b-43ae050dc01a

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 11 11 (RowCompute.rows[2]!) =
    (-3361804409470934976815286575571854038058592589603154165760000000 : ℤ) := by
  decide +kernel
