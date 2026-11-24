-- Prove2me | solution 1 for Hollom.C_inter_Icc_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:54:41.598797+00:00
-- url     : https://prove2.me/submissions/28539a13-adac-4d8d-8ff0-1367941c0f14

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
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_SpinalMap_injOn_of_isChain
import Theorems.Thm_Hollom_image_chainBetween_isChain
import Theorems.Thm_Hollom_card_chainBetween
import Theorems.Thm_Hollom_chainBetween_subset
import Theorems.Thm_Hollom_mapsTo_Icc_image
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
    xh + yh + 1 - (xl + yl) ≤ #{x ∈ (Icc (xl, yl) (xh, yh)).image (embed n) | x ∈ C} := by
  set int : Finset Hollom := (Icc (xl, yl) (xh, yh)).image (embed n)
  set I : Finset Hollom := {x ∈ int | x ∈ C}
  let D : Finset Hollom := (chainBetween xl yl xh yh).image (embed n)
  have hD : D ⊆ int := Finset.image_subset_image chainBetween_subset
  have D_maps : Set.MapsTo f D I := by
    simp only [I, Finset.coe_filter]
    exact ((mapsTo_Icc_image hC hlo hhi).mono_left hD).inter (by simp [Set.MapsTo])
  have f_inj : Set.InjOn f D := f.injOn_of_isChain image_chainBetween_isChain
  have : #D = xh + yh + 1 - (xl + yl) := by
    simp [D, Finset.card_image_of_injective, (embed n).injective, card_chainBetween hx hy]
  rw [← this]
  exact Finset.card_le_card_of_injOn f D_maps f_inj
end Hollom
