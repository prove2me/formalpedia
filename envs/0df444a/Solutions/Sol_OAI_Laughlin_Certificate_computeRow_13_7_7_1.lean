-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_7_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:29:29.270998+00:00
-- url     : https://prove2.me/submissions/bfb59fee-c128-4211-87fb-2c8f031790c3

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 7 7 (RowCompute.rows[1]!) =
    (314558512742283799011600986923223946275357867259199488000000 : ℤ) := by
  decide +kernel
