-- Prove2me | solution 1 for Hollom.square_subset_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:16:52.329443+00:00
-- url     : https://prove2.me/submissions/5c3678d5-f430-41bd-826b-092924163c91

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
import Theorems.Thm_Hollom_square_subset_above
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
variable {n : ℕ}
namespace Hollom
theorem _root_.solution (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ R n C \ (C ∩ level n) := by
  filter_upwards [square_subset_above h] with a ha
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  exact ⟨⟨by simp [embed_apply], fun b hb ↦ .inr ((ha ⟨_, hxy, rfl⟩).1 _ hb)⟩, (ha ⟨_, hxy, rfl⟩).2⟩
end Hollom
