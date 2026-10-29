-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:53:03.172404+00:00
-- url     : https://prove2.me/submissions/46886ab9-6131-4aa0-a9d3-85d2fc4543bf

import Mathlib
import Definitions.Def_OAIQ084L020

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : (Finset.univ : Finset (RowEntry 2)) = rowEntryData_2 := by
  decide +kernel
