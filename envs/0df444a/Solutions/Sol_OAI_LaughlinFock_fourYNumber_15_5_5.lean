-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:50:46.522964+00:00
-- url     : https://prove2.me/submissions/23fd09e6-1318-4f49-9c96-ddef4d460420

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 5 5 collectedFourData_15 : ℚ) / fourCommonDenominator = (-22143837937571892482195405511/268435456000000000000000) := by
  decide +kernel
