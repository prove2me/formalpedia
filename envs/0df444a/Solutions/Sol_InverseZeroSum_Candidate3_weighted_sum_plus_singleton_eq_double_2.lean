-- Prove2me | solution 2 for InverseZeroSum.Candidate3.weighted_sum_plus_singleton_eq_double
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:53.174317+00:00
-- url     : https://prove2.me/submissions/0d5ec416-6dfa-46c5-ac92-f5b6784ea7c3

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
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (A : Finset α) (f : α → M) (w : α → ℕ)
    {u : α} (hu : u ∈ A) (huOne : w u = 1)
    (hOther : ∀ x ∈ A.erase u, w x = 2) :
    (∑ x ∈ A, w x • f x) + f u =
      ∑ x ∈ A, (2 : ℕ) • f x := by
  have hErase :
      (∑ x ∈ A.erase u, w x • f x) =
        ∑ x ∈ A.erase u, (2 : ℕ) • f x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hOther x hx]
  rw [← Finset.sum_erase_add A (fun x => w x • f x) hu]
  rw [← Finset.sum_erase_add A (fun x => (2 : ℕ) • f x) hu]
  rw [hErase, huOne]
  simp [two_nsmul, add_assoc]
end InverseZeroSum.Candidate3
