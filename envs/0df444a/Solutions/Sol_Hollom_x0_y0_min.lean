-- Prove2me | solution 1 for Hollom.x0_y0_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:17:26.165478+00:00
-- url     : https://prove2.me/submissions/665c65c1-9edf-4ee5-8c0f-a50311c3af09

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
import Theorems.Thm_Hollom_x0y0_min

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (hC : IsChain (· ≤ ·) C) {a b : ℕ} (h : h(a, b, n + 1) ∈ C) :
    h(x0 n C, y0 n C, n + 1) ≤ h(a, b, n + 1) := x0y0_min (a, b) hC h
end Hollom
