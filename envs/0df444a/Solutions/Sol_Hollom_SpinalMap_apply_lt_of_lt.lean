-- Prove2me | solution 1 for Hollom.SpinalMap.apply_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:18:55.056035+00:00
-- url     : https://prove2.me/submissions/e73e4ddc-fe93-4866-a54f-5928db864714

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
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_not_lt_apply
attribute [local simp] Hollom.SpinalMap.mem

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {α : Type*} [PartialOrder α] {C : Set α}
open Hollom.SpinalMap
variable (f : SpinalMap C)
variable {x y z : α}
namespace Hollom.SpinalMap
theorem _root_.solution (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : x < y) : f x < y := by
  rcases hC.total (f.mem x) hy with h | h
  · rcases h.eq_or_lt with rfl | hlt
    · exact (f.not_lt_apply hx).elim
    · exact hlt
  · exact (f.not_lt_apply (hx.trans_le h)).elim
end Hollom.SpinalMap
