-- Prove2me | solution 1 for N4Code.colVal_eq_iff_colOfNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:55.886093+00:00
-- url     : https://prove2.me/submissions/9afb8606-596b-4a24-9e97-d46806f9ee0e

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
import Theorems.Thm_N4Code_colOfNat_colVal
import Theorems.Thm_N4Code_colVal_colOfNat

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (c : Column) (k : ℕ) (hk : k ≤ 15) :
    colVal c = k ↔ c = colOfNat k := by
  constructor
  · intro h
    rw [← colOfNat_colVal c, h]
  · intro h
    rw [h, colVal_colOfNat k hk]
end N4Code
