-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:50:31.954368+00:00
-- url     : https://prove2.me/submissions/6678369b-08a2-4138-b779-553fd2472909

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 13 5 collectedFourData_15 : ℚ) / fourCommonDenominator = (-104668576082860227329572569603/1342177280000000000000000) := by
  decide +kernel
