-- Prove2me | solution 1 for Hollom.card_C_inter_Icc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:42.463656+00:00
-- url     : https://prove2.me/submissions/73f48b3d-91cc-4ec8-bb37-1de33f34b0be

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
import Theorems.Thm_Hollom_line_injOn
import Theorems.Thm_Hollom_line_mapsTo
import Theorems.Thm_Hollom_embed_image_Icc
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_C_inter_Icc_large
attribute [local ext] Hollom.SpinalMap.ext
attribute [local simp] Hollom.SpinalMap.toFun_eq_coe
attribute [local simp] Hollom.SpinalMap.mem
attribute [local simp] Hollom.SpinalMap.idempotent

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
open Classical Finset
namespace Hollom
theorem _root_.solution (f : SpinalMap C) {n : ℕ} {xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hx : xl ≤ xh) (hy : yl ≤ yh)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) :
    #{x ∈ (Icc (xl, yl) (xh, yh)).image (embed n) | x ∈ C} = xh + yh + 1 - (xl + yl) := by
  set int : Finset Hollom := (Icc (xl, yl) (xh, yh)).image (embed n)
  set I : Finset Hollom := {x ∈ int | x ∈ C}
  have int_eq : int = Set.Icc h(xl, yl, n) h(xh, yh, n) := by
    simp only [coe_image, coe_Icc, int, embed_image_Icc]
  have hI : IsChain (· ≤ ·) (I : Set Hollom) := hC.mono (by simp [Set.subset_def, I])
  have hIn : (I : Set Hollom) ⊆ level n := by simp +contextual [Set.subset_def, I, int, embed_apply]
  have : Set.MapsTo line int (Icc (xl + yl) (xh + yh)) := by
    rw [int_eq, coe_Icc]
    exact line_mapsTo rfl
  replace this : Set.MapsTo line I (Icc (xl + yl) (xh + yh)) := this.mono_left (filter_subset _ _)
  refine le_antisymm ?_ (C_inter_Icc_large f hC hx hy hlo hhi)
  rw [← Nat.card_Icc]
  exact card_le_card_of_injOn _ this (line_injOn _ hI hIn)
end Hollom
