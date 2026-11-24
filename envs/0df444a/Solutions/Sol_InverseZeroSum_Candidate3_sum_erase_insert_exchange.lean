-- Prove2me | solution 1 for InverseZeroSum.Candidate3.sum_erase_insert_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:15.79386+00:00
-- url     : https://prove2.me/submissions/68863915-3d11-4e6c-83a6-584347597cb9

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (A : Finset α) (f : α → M) {x y : α}
    (hx : x ∉ A) (hy : y ∈ A) :
    (∑ i ∈ insert x (A.erase y), f i) + f y =
      (∑ i ∈ A, f i) + f x := by
  have hxErase : x ∉ A.erase y := by
    intro h
    exact hx (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hxErase]
  have hSplit := Finset.sum_erase_add A f hy
  calc
    f x + (∑ i ∈ A.erase y, f i) + f y =
        (∑ i ∈ A.erase y, f i) + f y + f x := by
      abel
    _ = (∑ i ∈ A, f i) + f x := by
      rw [hSplit]
end InverseZeroSum.Candidate3
