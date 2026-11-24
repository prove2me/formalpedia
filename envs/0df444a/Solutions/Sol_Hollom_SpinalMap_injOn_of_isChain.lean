-- Prove2me | solution 1 for Hollom.SpinalMap.injOn_of_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:57.740269+00:00
-- url     : https://prove2.me/submissions/ea83ba91-c21f-4e35-bac0-1d5e7ebac066

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
import Theorems.Thm_Hollom_SpinalMap_incomp_of_eq

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
theorem _root_.solution {D : Set α} (hD : IsChain (· ≤ ·) D) : D.InjOn f := by
  intro x hx y hy h
  by_contra! h'
  exact f.incomp_of_eq h h' (hD.total hx hy)
end Hollom.SpinalMap
