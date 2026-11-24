-- Prove2me | solution 1 for Hollom.apply_eq_of_line_eq_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:19:55.38985+00:00
-- url     : https://prove2.me/submissions/4a08d662-f5ad-466e-8629-48108d32af7d

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
import Theorems.Thm_Hollom_apply_eq_of_line_eq_step
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
namespace Hollom
theorem _root_.solution (f : SpinalMap C) {n xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) (hx : xl ≤ xh) (hy : yl ≤ yh)
    {x y k : ℕ}
    (h₁l : h(xl, yl, n) ≤ h(x + k, y, n)) (h₂l : h(xl, yl, n) ≤ h(x, y + k, n))
    (h₁h : h(x + k, y, n) ≤ h(xh, yh, n)) (h₂h : h(x, y + k, n) ≤ h(xh, yh, n)) :
    f h(x + k, y, n) = f h(x, y + k, n) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
      have : f h(x + (k + 1), y, n) = f h(x + k, y + 1, n) := by
        simp only [← add_assoc] at h₁l h₁h ⊢
        refine apply_eq_of_line_eq_step f hC hlo hhi hx hy h₁l ?_ h₁h ?_
        all_goals
          simp only [toHollom_le_toHollom_iff_fixed_right] at h₁l h₁h h₂l h₂h ⊢
          omega
      rw [this, ih, add_right_comm, add_assoc]
      all_goals
        simp only [toHollom_le_toHollom_iff_fixed_right] at h₁l h₁h h₂l h₂h ⊢
        omega
end Hollom
