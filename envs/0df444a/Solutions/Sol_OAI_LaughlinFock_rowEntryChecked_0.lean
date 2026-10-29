-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:52:32.953156+00:00
-- url     : https://prove2.me/submissions/6fab4b39-37a1-424e-8036-8556c12014c2

import Mathlib
import Definitions.Def_OAIQ084L020

attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : (Finset.univ : Finset (RowEntry 0)) = rowEntryData_0 := by
  decide +kernel
