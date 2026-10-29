-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:45:11.695355+00:00
-- url     : https://prove2.me/submissions/2a6401a6-a344-470d-9631-c3a09323b22a

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 15 7 collectedFourData_15 : ℚ) / fourCommonDenominator = (424557985372508681956282503483/10737418240000000000000000) := by
  decide +kernel
