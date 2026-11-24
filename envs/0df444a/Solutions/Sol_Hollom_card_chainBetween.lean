-- Prove2me | solution 1 for Hollom.card_chainBetween
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:34.171735+00:00
-- url     : https://prove2.me/submissions/5f689571-1f02-4cbc-af06-bb21951e0e03

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
open Finset
namespace Hollom
theorem _root_.solution {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    #(chainBetween a b c d) = c + d + 1 - (a + b) := by
  rw [chainBetween, if_pos ⟨hac, hbd⟩, card_union_of_disjoint, Finset.card_Icc_prod]
  · simp only [Icc_self, card_singleton, Nat.card_Icc, one_mul]
    rw [← Finset.Ico_map_sectR, card_map, Nat.card_Ico]
    omega
  · rw [disjoint_left]
    simp
    omega
end Hollom
