-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:55:02.799011+00:00
-- url     : https://prove2.me/submissions/8e6d9282-71a2-44ff-b944-a602e99bc949

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : collectNumericRowParts 13 0 = collectedFourData_13_0 := by
  decide +kernel
