-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:53:46.818452+00:00
-- url     : https://prove2.me/submissions/4b76bc0f-702e-4822-801e-c53b2e2eb450

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution (t : Fin 8) :
    collectNumericRowParts 13 t = collectedFourData_13 t := by
  revert t
  decide +kernel
