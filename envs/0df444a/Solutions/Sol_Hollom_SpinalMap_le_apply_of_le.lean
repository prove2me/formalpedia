-- Prove2me | solution 1 for Hollom.SpinalMap.le_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:18:46.736263+00:00
-- url     : https://prove2.me/submissions/9a7fa8d8-3738-4647-9dcf-cafb866c831b

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
import Theorems.Thm_Hollom_SpinalMap_not_apply_lt
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
theorem _root_.solution (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : y ≤ x) : y ≤ f x := by
  rcases hC.total hy (f.mem x) with h | h
  · exact h
  · rcases h.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (f.not_apply_lt (hlt.trans_le hx)).elim
end Hollom.SpinalMap
