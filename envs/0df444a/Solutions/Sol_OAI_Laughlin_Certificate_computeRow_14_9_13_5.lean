-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_9_13_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:05.861465+00:00
-- url     : https://prove2.me/submissions/ea50bcd1-c108-48bd-b139-01fe7808e0b6

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 9 13 (RowCompute.rows[5]!) =
    (-19697137831075807807226815892240648845734105018204684288000000 : ℤ) := by
  decide +kernel
