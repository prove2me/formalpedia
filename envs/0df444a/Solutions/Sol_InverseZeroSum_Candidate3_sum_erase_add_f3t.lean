-- Prove2me | solution 1 for InverseZeroSum.Candidate3.sum_erase_add_f3t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:50.024879+00:00
-- url     : https://prove2.me/submissions/b510a3f8-7703-4540-9d32-063169afeaf7

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → F3T) {a : α} (ha : a ∈ A) :
    (∑ x ∈ A.erase a, f x) + f a = ∑ x ∈ A, f x := by
  exact Finset.sum_erase_add A f ha
end InverseZeroSum.Candidate3
