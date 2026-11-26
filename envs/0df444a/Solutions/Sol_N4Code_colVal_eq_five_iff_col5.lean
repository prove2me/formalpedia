-- Prove2me | solution 1 for N4Code.colVal_eq_five_iff_col5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:33.292196+00:00
-- url     : https://prove2.me/submissions/d23b0096-bf97-476b-861e-34e90f6a26de

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
theorem _root_.solution (c : Column) : colVal c = 5 ↔ c = col5 := by
  simpa [show colOfNat 5 = col5 by decide] using (colVal_eq_iff_colOfNat c 5 (by norm_num))
end N4Code
