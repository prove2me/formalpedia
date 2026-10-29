-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:56:46.850165+00:00
-- url     : https://prove2.me/submissions/be88cb4c-f920-4bc9-b155-09dfd77456ec

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 1 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (1308564550559617459628590378527219/838860800000000000000000) := by
  decide +kernel
