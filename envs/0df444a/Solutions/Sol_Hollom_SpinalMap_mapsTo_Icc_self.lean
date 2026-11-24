-- Prove2me | solution 1 for Hollom.SpinalMap.mapsTo_Icc_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:32:42.883791+00:00
-- url     : https://prove2.me/submissions/76527484-75cd-4db9-9e3e-7b8ee2615af5

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
import Theorems.Thm_Hollom_SpinalMap_apply_mem_Icc_of_mem_Icc

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
theorem _root_.solution (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hz : z ∈ C) :
    Set.MapsTo f (Set.Icc y z) (Set.Icc y z) := fun _ ↦ apply_mem_Icc_of_mem_Icc _ hC hy hz
end Hollom.SpinalMap
