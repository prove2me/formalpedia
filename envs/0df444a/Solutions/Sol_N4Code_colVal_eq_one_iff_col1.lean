-- Prove2me | solution 1 for N4Code.colVal_eq_one_iff_col1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:31.276013+00:00
-- url     : https://prove2.me/submissions/17cf6c9f-1fe0-45cf-b042-43e4a26a4c10

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
import Theorems.Thm_N4Code_colVal_eq_iff_colOfNat

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (c : Column) : colVal c = 1 ↔ c = col1 := by
  simpa [show colOfNat 1 = col1 by decide] using (colVal_eq_iff_colOfNat c 1 (by norm_num))
end N4Code
