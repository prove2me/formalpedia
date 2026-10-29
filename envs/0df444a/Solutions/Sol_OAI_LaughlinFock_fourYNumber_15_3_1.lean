-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:55:19.209194+00:00
-- url     : https://prove2.me/submissions/a6e216d6-0f3a-46da-8e47-a3a991990c54

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 3 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (55806599899143061188549474278133/335544320000000000000000) := by
  decide +kernel
