-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_7_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:53.108035+00:00
-- url     : https://prove2.me/submissions/1abdea37-a7f0-4325-b2b4-9d6c0e656deb

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 14 7 7 (RowCompute.rows[4]!) =
    (-25913627650419540903169727985051829205138214571110039552000000 : ℤ) := by
  decide +kernel
