-- Prove2me | solution 1 for Hollom.chainBetween_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:35.081812+00:00
-- url     : https://prove2.me/submissions/c1547984-ef12-4eb8-8b0f-0b538799810b

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
open Finset
namespace Hollom
theorem _root_.solution {a b c d : ℕ} :
    chainBetween a b c d ⊆ Finset.Icc (a, b) (c, d) := by
  unfold chainBetween
  split_ifs with h
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc, Prod.mk_le_mk, Prod.lt_iff] at hp ⊢
    rcases hp with ⟨⟨h1, h2⟩, hlt⟩ | ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · rcases hlt with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    · omega
  · exact Finset.empty_subset _
end Hollom
