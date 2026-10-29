-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:48:52.699574+00:00
-- url     : https://prove2.me/submissions/e3575222-a52c-408a-b1f4-50a48a7c08d0

import Mathlib
import Definitions.Def_OAIQ084L015
import Definitions.Def_OAIQ084L020


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    rowEntryList_2.map (rowToNumeric ⟨2, by decide⟩) = numericRowData_2 := by
  decide +kernel
