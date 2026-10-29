-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:50:20.889019+00:00
-- url     : https://prove2.me/submissions/92bffb56-20f0-4937-8814-fdb2e614aa3c

import Mathlib
import Definitions.Def_OAIQ084L015


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    rowEntryList_3.map (rowToNumeric ⟨3, by decide⟩) = numericRowData_3 := by
  decide +kernel
