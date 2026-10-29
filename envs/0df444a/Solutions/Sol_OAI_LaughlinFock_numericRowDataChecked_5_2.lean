-- Prove2me | solution 2 for OAI.LaughlinFock.numericRowDataChecked_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:52:55.609854+00:00
-- url     : https://prove2.me/submissions/8c5d67f3-dfcd-492a-b7ca-012c6661fd4a

import Mathlib
import Definitions.Def_OAIQ084L015


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    rowEntryList_5.map (rowToNumeric ⟨5, by decide⟩) = numericRowData_5 := by
  decide +kernel
