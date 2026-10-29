-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:54:54.49967+00:00
-- url     : https://prove2.me/submissions/2a4215f6-f026-420d-83a2-1dc1a96563df

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : collectNumericRowParts 13 3 = collectedFourData_13_3 := by
  decide +kernel
