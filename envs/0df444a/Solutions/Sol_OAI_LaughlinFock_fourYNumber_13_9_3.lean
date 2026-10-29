-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:46:43.365011+00:00
-- url     : https://prove2.me/submissions/7103e419-a792-4ae8-af1f-e17d6c4fb9a0

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 9 3 collectedFourData_13 : ℚ) / fourCommonDenominator = (-83467340369805263164603981947/26843545600000000000000000) := by
  decide +kernel
