-- Prove2me | solution 1 for Hollom.exists_partition_iff_nonempty_spinalMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:13:29.220842+00:00
-- url     : https://prove2.me/submissions/929a08ae-2fef-4f41-83ba-661343e7fa22

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
import Theorems.Thm_Hollom_SpinalMap_fibre_antichain
import Theorems.Thm_Hollom_SpinalMap_idempotent
import Theorems.Thm_chain_intersect_antichain

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
namespace Hollom
theorem _root_.solution
    {α : Type*} [PartialOrder α] {C : Set α} (hC : IsChain (· ≤ ·) C) :
    (∃ S, Setoid.IsPartition S ∧ ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) ↔
      Nonempty (SpinalMap C) := by
  constructor
  · rintro ⟨S, ⟨hSemp, hS⟩, hSA⟩
    simp only [ExistsUnique, and_imp, and_assoc] at hS
    simp only [Set.Nonempty, Set.mem_inter_iff] at hSA
    choose F hFS hFmem hFuniq using hS
    choose hA G hGA hGC using hSA
    let f (x : α) : α := G (F x) (hFS x)
    have hfCid (x : α) (hx : x ∈ C) : f x = x :=
      chain_intersect_antichain hC (hA (F x) (hFS _)) ⟨hGC _ _, hGA _ _⟩ ⟨hx, hFmem _⟩
    have hf (x : α) : IsAntichain (· ≤ ·) (f ⁻¹' {x}) := (hA (F x) (hFS _)).subset <| by
      rintro y rfl
      exact hFuniq (f y) (F y) (hFS y) (hGA _ _) ▸ hFmem _
    exact ⟨⟨f, fun x ↦ hGC _ _, hfCid, hf⟩⟩
  · rintro ⟨f⟩
    refine ⟨_, (Setoid.ker f).isPartition_classes, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ⟨f.fibre_antichain _, f x, by simp [Setoid.ker, Function.onFun]⟩
end Hollom
