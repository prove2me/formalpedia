-- Prove2me | solution 1 for Hollom.not_S_hits_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:05.856806+00:00
-- url     : https://prove2.me/submissions/2f8bd34c-0938-4cfb-9fa1-c83894c77f96

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
import Theorems.Thm_Hollom_add_lt_add_of_lt
import Theorems.Thm_Hollom_SpinalMap_ext
import Theorems.Thm_Hollom_SpinalMap_toFun_eq_coe
import Theorems.Thm_Hollom_SpinalMap_mem
import Theorems.Thm_Hollom_SpinalMap_eq_self_of_mem
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_Hollom_SpinalMap_not_le_of_eq
import Theorems.Thm_Hollom_SpinalMap_incomp_apply
import Theorems.Thm_Hollom_apply_eq_of_line_eq
import Theorems.Thm_Hollom_R_subset_level
import Theorems.Thm_Hollom_x0_y0_mem
import Theorems.Thm_Hollom_x0_y0_min
import Theorems.Thm_Hollom_S_subset_level
import Theorems.Thm_Hollom_left_or_right_bias
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
theorem _root_.solution (f : SpinalMap C) (hC : IsChain (· ≤ ·) C)
    {x : Hollom} (hx : x ∈ S n C) (hx' : x ∉ C ∩ level n) :
    f x ∉ C ∩ level (n + 1) := by
  cases (C ∩ level (n + 1)).finite_or_infinite
  -- In the case that `C ∩ level (n + 1)` is finite, this is immediate from the definition of `S`.
  case inl h =>
    rw [S, if_pos h, Set.mem_setOf_eq] at hx
    intro hy
    refine f.incomp_apply ?_ (hx.2 _ hy).symm
    have := R_subset_level hx.1
    simp only [level_eq, Set.mem_setOf_eq] at this
    intro h
    simp [level_eq, h, this] at hy

  -- So suppose it is infinite
  case inr h =>
    -- Write `(x, y, n)` for our given point, and set `(a, b, n + 1) := f(x, y, n)`
    induction S_subset_level hx using induction_on_level with | h x y =>
    simp only [S, if_neg h, Set.mem_setOf_eq, ofHollom_toHollom] at hx
    intro hp
    set fp := f h(x, y, n) with hfp
    clear_value fp
    induction hp.2 using induction_on_level with | h a b =>
    clear fp
    -- Certainly `x0 ≤ a` and `y0 ≤ b`
    obtain ⟨ha, hb⟩ : x0 n C ≤ a ∧ y0 n C ≤ b := by simpa using x0_y0_min hC hp.1
    -- Either `C ∩ level (n + 1)` stretches far left or far right: both cases are symmetric
    obtain (rbias | lbias) := left_or_right_bias (x0 n C) (y0 n C) (fun x y ↦ x0_y0_min hC) h
    · obtain ⟨j, hjCn, hj⟩ := rbias (a + b - x0 n C)
      -- If it goes to the right, take `j ∈ C` such that `(x0, a + b - x0, n + 1) ≤ j`
      -- Then we have `(a, b, n + 1) ≤ j`...
      have hj' : h(a, b, n + 1) ≤ j := by
        induction hjCn.2 using induction_on_level with | h c d =>
        rcases hC.total hp.1 hjCn.1 with hle | hle
        · exact hle
        · rcases hle.eq_or_lt with heq | hlt
          · exact heq.ge
          · have : c + d < a + b := add_lt_add_of_lt hlt
            simp only [toHollom_le_toHollom_iff_fixed_right] at hj
            omega
      -- ...and `(x0, y0, n + 1) ≤ j`.
      have h0j : h(x0 n C, y0 n C, n + 1) ≤ j := hj'.trans' (by simp [ha, hb])
      have : line h(a, b, n + 1) = line h(x0 n C, a + b - x0 n C, n + 1) := by simp; omega
      -- Then we have `f(a, b, n + 1) = f(x0, a + b - x0, n + 1)` since they are at the same line
      have : f h(a, b, n + 1) = f h(x0 n C, a + b - x0 n C, n + 1) := apply_eq_of_line_eq f hC
        ⟨x0_y0_mem h.nonempty, by simp⟩ hjCn ‹_› this (x0_y0_min hC hp.1) (by simp; omega) hj' hj
      -- so `f(x, y, n) = (a, b, n + 1) = f(a, b, n + 1) = f(x0, a + b - x0, n + 1)`
      have : f h(x, y, n) = f h(x0 n C, a + b - x0 n C, n + 1) := by
        rw [← this, ← hfp, f.eq_self_of_mem hp.1]
      -- But `(x0 n C, a + b - x0 n C, n + 1) ≤ (x, y, n)` since `(x, y, n)` is in `S`, giving
      -- a contradiction since they are in the same fibre.
      exact f.not_le_of_eq this.symm (by simp) (.next_min (hx.2.trans' (by simp)))
    · obtain ⟨j, hjCn, hj⟩ := lbias (a + b - y0 n C)
      -- The left case is exactly symmetric
      have hj' : h(a, b, n + 1) ≤ j := by
        induction hjCn.2 using induction_on_level with | h c d =>
        rcases hC.total hp.1 hjCn.1 with hle | hle
        · exact hle
        · rcases hle.eq_or_lt with heq | hlt
          · exact heq.ge
          · have : c + d < a + b := add_lt_add_of_lt hlt
            simp only [toHollom_le_toHollom_iff_fixed_right] at hj
            omega
      have h0j : h(x0 n C, y0 n C, n + 1) ≤ j := hj'.trans' (by simp [ha, hb])
      have : line h(a, b, n + 1) = line h(a + b - y0 n C, y0 n C, n + 1) := by simp; omega
      have := apply_eq_of_line_eq f hC ⟨x0_y0_mem h.nonempty, by simp⟩ hjCn ‹_› this
        (x0_y0_min hC hp.1) (by simp; omega) hj' hj
      have : f h(x, y, n) = f h(a + b - y0 n C, y0 n C, n + 1) := by
        rw [← this, ← hfp, f.eq_self_of_mem hp.1]
      exact f.not_le_of_eq this.symm (by simp) (.next_min (hx.2.trans' (by simp)))
end Hollom
