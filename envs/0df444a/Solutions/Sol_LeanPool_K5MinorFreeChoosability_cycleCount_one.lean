-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cycleCount_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:46.792392+00:00
-- url     : https://prove2.me/submissions/ffa346ef-f38f-4344-8f7f-98954886e0b1

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
omit [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution : cycleCount (1 : Perm α) = Nat.card α := by
  unfold cycleCount numClasses
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift id ?_) ⟨?_, ?_⟩)
  · intro a b h
    obtain ⟨i, hi⟩ := h
    simpa using hi
  · intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    exact Quotient.sound (show SameCycle 1 a b from ⟨0, by simpa using hpq⟩)
  · intro a
    exact ⟨Quotient.mk _ a, rfl⟩
end LeanPool.K5MinorFreeChoosability
