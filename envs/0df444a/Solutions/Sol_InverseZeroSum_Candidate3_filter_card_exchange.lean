-- Prove2me | solution 1 for InverseZeroSum.Candidate3.filter_card_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:15.952796+00:00
-- url     : https://prove2.me/submissions/74beac5a-4ce3-4665-b75d-6340fb364dc3

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) {x y : α}
    (hx : x ∉ A) (hy : y ∈ A) (v : β) :
    ((insert x (A.erase y)).filter (fun z => f z = v)).card +
        (if f y = v then 1 else 0) =
      (A.filter (fun z => f z = v)).card +
        (if f x = v then 1 else 0) := by
  classical
  have hxErase : x ∉ A.erase y := by
    intro h
    exact hx (Finset.mem_of_mem_erase h)
  by_cases hvx : f x = v <;> by_cases hvy : f y = v
  all_goals simp [Finset.filter_insert, Finset.filter_erase,
    hvx, hvy, hxErase, hx, hy, Finset.card_erase_of_mem]
  all_goals
    have hPos : 0 < (A.filter (fun z => f z = v)).card := by
      apply Finset.card_pos.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, hvy⟩⟩
    omega
end InverseZeroSum.Candidate3
