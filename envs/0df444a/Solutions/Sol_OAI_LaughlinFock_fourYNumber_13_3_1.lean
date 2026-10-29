-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:51:39.206807+00:00
-- url     : https://prove2.me/submissions/dbebb768-b8aa-4ef4-a572-396a7e583a8c

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 3 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (1123748024618949361656403709187/2684354560000000000000000) := by
  decide +kernel
