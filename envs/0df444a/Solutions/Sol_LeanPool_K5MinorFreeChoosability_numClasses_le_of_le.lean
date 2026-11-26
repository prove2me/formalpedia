-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.numClasses_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:29.238672+00:00
-- url     : https://prove2.me/submissions/4bf4dda7-30d5-4a23-bec4-63d2292e7ae9

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite α] {s t : Setoid α} (h : ∀ a b, s a b → t a b) :
    numClasses t ≤ numClasses s := by
  refine Nat.card_le_card_of_surjective
    (Quotient.lift (fun a => Quotient.mk t a) (fun a b hab => Quotient.sound (h a b hab))) ?_
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨Quotient.mk s a, rfl⟩
end LeanPool.K5MinorFreeChoosability
