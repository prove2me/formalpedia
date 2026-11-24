-- Prove2me | solution 1 for Hollom.left_or_right_bias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:14:59.820388+00:00
-- url     : https://prove2.me/submissions/6e85eda1-fc8a-49ff-8dbc-3b13bf40c7fa

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
theorem _root_.solution {n : ℕ} (a b : ℕ)
    (hab : ∀ x y, h(x, y, n) ∈ C → h(a, b, n) ≤ h(x, y, n))
    (hCn : (C ∩ level n).Infinite) :
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, h(a, i, n) ≤ j) ∨
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, h(i, b, n) ≤ j) := by
  -- Suppose otherwise, and take `c` and `d` counterexamples to both alternatives
  by_contra! h
  obtain ⟨⟨c, hc⟩, d, hd⟩ := h
  -- Observe the set of points in `C ∩ level n` below `(d, c, n)` is finite, and aim to show that
  -- `C ∩ level n` is contained in this set, for a contradiction
  refine hCn (((Set.finite_Iic (d, c)).image (embed n)).subset ?_)
  simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_image, Set.mem_Iic, Prod.exists,
    Prod.mk_le_mk, and_imp, «forall», toHollom_mem_level_iff, Prod.forall]
  rintro x y n hxy rfl
  specialize hab x y (by simp [hxy])
  specialize hc h(x, y, n) (by simp [hxy])
  specialize hd h(x, y, n) (by simp [hxy])
  simp_all only [toHollom_le_toHollom_iff_fixed_right, true_and, not_le, and_true]
  exact ⟨_, _, ⟨hd.le, hc.le⟩, rfl⟩
end Hollom
