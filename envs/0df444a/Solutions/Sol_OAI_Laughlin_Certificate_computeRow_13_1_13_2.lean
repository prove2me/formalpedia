-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_13_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:13:45.109989+00:00
-- url     : https://prove2.me/submissions/95a6bf1e-5e71-4063-8d54-5b8fdbe3d113

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 13 (RowCompute.rows[2]!) =
    (134590818607773831156282751405430961922033800033588297596928000000 : ℤ) := by
  decide +kernel
