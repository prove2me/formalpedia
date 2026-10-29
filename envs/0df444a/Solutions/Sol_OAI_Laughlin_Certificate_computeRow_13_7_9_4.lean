-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:19.453985+00:00
-- url     : https://prove2.me/submissions/a1e6005b-dc16-4c8f-9d58-162db1af2ad0

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 9 (RowCompute.rows[4]!) =
    (470362093977206839881450280156877072252055975006044160000000 : ℤ) := by
  decide +kernel
