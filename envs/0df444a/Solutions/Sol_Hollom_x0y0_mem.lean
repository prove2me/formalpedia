-- Prove2me | solution 1 for Hollom.x0y0_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:54.532585+00:00
-- url     : https://prove2.me/submissions/f2720960-801f-4245-9548-494db17749e8

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

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (h : (C ∩ level (n + 1)).Nonempty) :
    embed (n + 1) (x0y0 n C) ∈ C := by
  rw [x0y0, dif_pos h]
  exact WellFounded.min_mem _ {x | embed (n + 1) x ∈ C} _
end Hollom
