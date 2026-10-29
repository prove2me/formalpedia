-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:45:00.128891+00:00
-- url     : https://prove2.me/submissions/4db6712d-18ef-4126-bc25-61ca37867214

import Mathlib
import Definitions.Def_OAIQ084L020

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : (Finset.univ : Finset (RowEntry 7)) = rowEntryData_7 := by
  decide +kernel
