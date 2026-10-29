-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:59:07.565996+00:00
-- url     : https://prove2.me/submissions/0867686d-ab8b-4be4-a58f-bb3b7a9477c4

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 9 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (-53299623602193211938552243903/3355443200000000000000000) := by
  decide +kernel
