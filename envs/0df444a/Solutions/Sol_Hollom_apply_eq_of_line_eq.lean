-- Prove2me | solution 1 for Hollom.apply_eq_of_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:32.140803+00:00
-- url     : https://prove2.me/submissions/5d2c455b-6d10-433b-afbb-0da665bfd4a3

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
import Theorems.Thm_Hollom_apply_eq_of_line_eq_aux
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
theorem _root_.solution (f : SpinalMap C) {n : ℕ} (hC : IsChain (· ≤ ·) C)
    {lo hi : Hollom} (hlo : lo ∈ C ∩ level n) (hhi : hi ∈ C ∩ level n) (hlohi : lo ≤ hi)
    {x y : Hollom} (h : line x = line y)
    (h₁l : lo ≤ x) (h₂l : lo ≤ y) (h₁h : x ≤ hi) (h₂h : y ≤ hi) :
    f x = f y := by
  wlog hxy : (ofHollom y).1 ≤ (ofHollom x).1 generalizing x y
  · exact (this h.symm h₂l h₁l h₂h h₁h (le_of_not_ge hxy)).symm
  have hx : x ∈ level n := ordConnected_level.out hlo.2 hhi.2 ⟨h₁l, h₁h⟩
  have hy : y ∈ level n := ordConnected_level.out hlo.2 hhi.2 ⟨h₂l, h₂h⟩
  induction hx using induction_on_level with | h x₁ y₁ =>
  induction hy using induction_on_level with | h x₂ y₂ =>
  simp only [ofHollom_toHollom] at hxy
  simp only [line_toHollom] at h
  obtain ⟨k, rfl⟩ := exists_add_of_le hxy
  obtain rfl : y₂ = y₁ + k := by omega
  induction hlo.2 using induction_on_level with | h xlo ylo =>
  induction hhi.2 using induction_on_level with | h xhi yhi =>
  exact apply_eq_of_line_eq_aux f hC hlo.1 hhi.1 (by simp_all) (by simp_all) h₁l h₂l h₁h h₂h
end Hollom
