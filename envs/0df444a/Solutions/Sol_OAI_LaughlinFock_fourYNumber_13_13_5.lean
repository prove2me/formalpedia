-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:49:48.243123+00:00
-- url     : https://prove2.me/submissions/16e01465-7c47-4115-a1b4-e04fa4003275

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 13 5 collectedFourData_13 : ℚ) / fourCommonDenominator = (946650494523480527937150423/268435456000000000000000) := by
  decide +kernel
