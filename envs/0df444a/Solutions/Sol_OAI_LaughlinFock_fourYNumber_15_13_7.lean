-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:57:24.954244+00:00
-- url     : https://prove2.me/submissions/3ee2bbce-575d-429c-a29f-cbe3778c95ea

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 13 7 collectedFourData_15 : ℚ) / fourCommonDenominator = (6517014895586416110380281791/6710886400000000000000000) := by
  decide +kernel
