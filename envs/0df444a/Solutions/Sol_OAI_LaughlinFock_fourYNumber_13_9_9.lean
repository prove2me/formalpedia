-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_9_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:53:21.013562+00:00
-- url     : https://prove2.me/submissions/b4df0c24-30d3-4723-98bc-2e67ae5c6e20

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 9 9 collectedFourData_13 : ℚ) / fourCommonDenominator = (-6983205275787585443985353589/26843545600000000000000000) := by
  decide +kernel
