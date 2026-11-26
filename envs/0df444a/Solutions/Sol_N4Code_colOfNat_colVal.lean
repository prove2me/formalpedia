-- Prove2me | solution 1 for N4Code.colOfNat_colVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:21.717052+00:00
-- url     : https://prove2.me/submissions/75043869-7040-41a0-8718-feb3ef7bfd27

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
import Theorems.Thm_N4Code_colBit_eq_testBit

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (c : Column) : colOfNat (colVal c) = c := by
  funext r
  simpa [colBit, colOfNat] using (colBit_eq_testBit c r).symm
end N4Code
