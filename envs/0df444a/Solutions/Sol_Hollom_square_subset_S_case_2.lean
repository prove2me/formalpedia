-- Prove2me | solution 1 for Hollom.square_subset_S_case_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:20:48.275841+00:00
-- url     : https://prove2.me/submissions/2bd7dfd9-68ed-47fe-af20-28877e253a02

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
import Theorems.Thm_Hollom_square_subset_R
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
theorem _root_.solution (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Infinite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) := by
  rw [S, if_neg h']
  filter_upwards [eventually_ge_atTop (x0 n C + 1), eventually_ge_atTop (y0 n C + 1),
    square_subset_R h] with a hax hay haR
  aesop (add simp embed_apply) <;> omega
end Hollom
