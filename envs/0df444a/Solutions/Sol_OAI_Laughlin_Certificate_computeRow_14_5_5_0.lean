-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_5_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:41:27.622238+00:00
-- url     : https://prove2.me/submissions/dde72f45-c4f1-42de-bd9d-073f224138cc

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 5 5 (RowCompute.rows[0]!) =
    (720558515009241396311592199429830575223211232580278943744000000 : ℤ) := by
  decide +kernel
