-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:52:25.6491+00:00
-- url     : https://prove2.me/submissions/0ba6ac6c-5306-43f3-959b-c1c0bbe324fb

import Mathlib
import Definitions.Def_OAIQ084L015

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : (Finset.univ : Finset (RowEntry 4)) = rowEntryData_4 := by
  decide +kernel
