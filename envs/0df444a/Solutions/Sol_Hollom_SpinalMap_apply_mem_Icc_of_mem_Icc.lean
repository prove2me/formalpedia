-- Prove2me | solution 1 for Hollom.SpinalMap.apply_mem_Icc_of_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:24:25.500856+00:00
-- url     : https://prove2.me/submissions/ff5eecec-1bd2-4ffb-8631-c1649977cc66

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
import Theorems.Thm_Hollom_SpinalMap_le_apply_of_le
import Theorems.Thm_Hollom_SpinalMap_apply_le_of_le

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
theorem _root_.solution (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hz : z ∈ C)
    (hx : x ∈ Set.Icc y z) : f x ∈ Set.Icc y z :=
  ⟨f.le_apply_of_le hC hy hx.1, f.apply_le_of_le hC hz hx.2⟩
end Hollom.SpinalMap
