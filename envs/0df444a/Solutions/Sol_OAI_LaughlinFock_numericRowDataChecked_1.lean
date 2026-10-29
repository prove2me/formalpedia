-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:49:00.773328+00:00
-- url     : https://prove2.me/submissions/a2b8bdc1-371b-4e53-af6c-197992dd537a

import Mathlib
import Definitions.Def_OAIQ084L015
import Definitions.Def_OAIQ084L020


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    rowEntryList_1.map (rowToNumeric ⟨1, by decide⟩) = numericRowData_1 := by
  decide +kernel
