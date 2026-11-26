-- Prove2me | solution 1 for N4Code.colBit_eq_testBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:44.539903+00:00
-- url     : https://prove2.me/submissions/02f07f83-4fa0-43a1-9235-b75c68be2624

import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_N4Code_Definitions

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (c : Column) (j : Fin 4) :
    colBit j c = (colVal c).testBit (3 - j.val) := by
  have h : ∀ (c : Column) (j : Fin 4),
      colBit j c = (colVal c).testBit (3 - j.val) := by
    decide
  exact h c j
end N4Code
