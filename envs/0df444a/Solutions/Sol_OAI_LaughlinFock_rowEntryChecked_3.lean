-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:51:46.706278+00:00
-- url     : https://prove2.me/submissions/07e03ca8-d496-4b8f-98db-c26cdf4af139

import Mathlib
import Definitions.Def_OAIQ084L015

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : (Finset.univ : Finset (RowEntry 3)) = rowEntryData_3 := by
  decide +kernel
