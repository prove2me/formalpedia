-- Prove2me | solution 1 for Hollom.S_mapsTo_previous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:49.417588+00:00
-- url     : https://prove2.me/submissions/abefa03d-ee92-40bc-a057-6bac478324c6

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
import Theorems.Thm_Hollom_SpinalMap_eq_of_le
import Theorems.Thm_Hollom_not_R_hits_same
import Theorems.Thm_Hollom_S_subset_R
import Theorems.Thm_Hollom_S_subset_level
import Theorems.Thm_Hollom_not_S_hits_next
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
theorem _root_.solution (f : SpinalMap C) (hC : IsChain (· ≤ ·) C) (hn : n ≠ 0) :
    ∀ x ∈ S n C \ (C ∩ level n), f x ∈ C ∩ level (n - 1) := by
  -- Clearly it must be mapped into `C`
  intro x hx
  refine ⟨f.mem _, ?_⟩
  set p := f x with hp
  clear_value p
  induction S_subset_level hx.1 using induction_on_level with | h x y =>
  induction p with | h a b m =>
  -- Now write `(x, y, n)` for our given point, and suppose it is mapped to `(a, b, m)`.
  simp only [toHollom_mem_level_iff]
  -- We must have `m ≠ n`, as `(x, y, n) ∈ R` and no point of `R` can map to `C ∩ level n`
  have : m ≠ n := by
    rintro rfl
    have : f _ ∉ _ := not_R_hits_same (S_subset_R hx.1) hx.2
    simp only [Set.mem_inter_iff, SpinalMap.mem, true_and] at this
    simp [← hp] at this
  -- Furthermore, we must have `n + 1 ≠ m`, as `(x, y, n) ∈ S` and no point of `S` can map to
  -- `C ∩ level (n + 1)`.
  have : n + 1 ≠ m := by
    rintro rfl
    have : f _ ∉ _ := not_S_hits_next f hC hx.1 hx.2
    simp only [Set.mem_inter_iff, SpinalMap.mem, true_and] at this
    simp [← hp] at this
  -- Next `f (a, b, m) = (a, b, m) = f (x, y, n)`
  have hp' : f h(a, b, m) = f h(x, y, n) := by
    rw [hp, f.idempotent]
  -- But `(x, y, n) ≤ (a, b, m)` if `m + 2 ≤ n`, so this cannot hold
  have : ¬ m + 2 ≤ n := by
    intro h
    have := f.eq_of_le hp'.symm (.twice h)
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at this
    omega
  -- and `(a, b, m) ≤ (x, y, n)` if `n + 2 ≤ m`, so this cannot hold either
  have : ¬ n + 2 ≤ m := by
    intro h
    have := f.eq_of_le hp' (.twice h)
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at this
    omega
  -- So the only remaining option is that `m = n - 1`.
  omega
end Hollom
