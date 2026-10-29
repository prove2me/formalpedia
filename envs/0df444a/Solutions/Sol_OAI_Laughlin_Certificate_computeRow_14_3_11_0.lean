-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_3_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:44:12.906053+00:00
-- url     : https://prove2.me/submissions/b110c089-94c9-4c7b-8520-05bcd2b1c6d5

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 3 11 (RowCompute.rows[0]!) =
    (8445460416531936171378284945051163012489963898073379766272000000 : ℤ) := by
  decide +kernel
