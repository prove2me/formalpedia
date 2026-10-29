-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_9_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:46:18.969694+00:00
-- url     : https://prove2.me/submissions/136e352f-0266-49bd-8ac9-0a9012d772dd

import Mathlib
import Definitions.Def_OAIQ047L000

open OAI.Laughlin.Certificate in
theorem solution : RowCompute.yRowIntegralFast 13 9 9 (RowCompute.rows[3]!) =
    (88854151281206089614544627847319726852299111656845213696000000 : ℤ) := by
  decide +kernel
