-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_11_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:56:04.989756+00:00
-- url     : https://prove2.me/submissions/4f55f043-ddcc-4a45-840c-f7a65bd6ea95

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 11 7 collectedFourData_15 : ℚ) / fourCommonDenominator = (-97616174744145272084505558153/26843545600000000000000000) := by
  decide +kernel
