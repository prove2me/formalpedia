-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_12_3_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:42:46.763555+00:00
-- url     : https://prove2.me/submissions/cc34b7f3-6ef4-4296-80b4-30e947bdbc92

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[0]!) =
    (-25875316937120714040935923332472621826321982773482487808000000 : ℤ) := by
  decide +kernel
