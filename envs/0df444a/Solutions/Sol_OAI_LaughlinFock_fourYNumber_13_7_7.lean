-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_7_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:48:21.460848+00:00
-- url     : https://prove2.me/submissions/289fb2eb-415f-496d-a717-c5b7d6d18294

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 7 7 collectedFourData_13 : ℚ) / fourCommonDenominator = (36229772664258699428237933199/85899345920000000000000000) := by
  decide +kernel
