-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:47:25.04669+00:00
-- url     : https://prove2.me/submissions/5f2ca744-4e80-46ce-aaad-7a0c783700bf

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 1 3 (RowCompute.rows[4]!) =
    (175166574423452065720552273661311293783748709399295688704000000 : ℤ) := by
  decide +kernel
