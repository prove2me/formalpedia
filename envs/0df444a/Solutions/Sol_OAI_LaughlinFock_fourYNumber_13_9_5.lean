-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:48:44.964119+00:00
-- url     : https://prove2.me/submissions/2c0d8705-e8bc-491c-8e77-3d1b90b1ea13

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 9 5 collectedFourData_13 : ℚ) / fourCommonDenominator = (4274996279199192620771589153/2684354560000000000000000) := by
  decide +kernel
