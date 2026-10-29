-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_5_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:45:21.102979+00:00
-- url     : https://prove2.me/submissions/eb19741f-a9cf-4299-b822-60a9e10364a9

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 5 5 (RowCompute.rows[1]!) =
    (163504840710920698256181545543616620789410682256752640000000 : ℤ) := by
  decide +kernel
