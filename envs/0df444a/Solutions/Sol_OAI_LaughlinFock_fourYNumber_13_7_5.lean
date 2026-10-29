-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:47:24.435437+00:00
-- url     : https://prove2.me/submissions/84bcc4b8-e00c-4fae-99c0-bf6a3351306d

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 7 5 collectedFourData_13 : ℚ) / fourCommonDenominator = (-5970782558191454823931610373/53687091200000000000000000) := by
  decide +kernel
