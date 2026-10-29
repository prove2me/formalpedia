-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:44:52.085531+00:00
-- url     : https://prove2.me/submissions/699a47ec-f30b-4342-9145-5ee4d9e03e28

import Mathlib
import Definitions.Def_OAIQ084L015

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : (Finset.univ : Finset (RowEntry 6)) = rowEntryData_6 := by
  decide +kernel
