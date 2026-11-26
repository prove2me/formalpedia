-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.numClasses_congr_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:33.339326+00:00
-- url     : https://prove2.me/submissions/89092b5a-b853-46b3-9aeb-c0d01558a23d

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
theorem _root_.solution {β : Type*} {s : Setoid α} {t : Setoid β} (e : α ≃ β)
    (h : ∀ a b, s a b ↔ t (e a) (e b)) : numClasses s = numClasses t :=
  Nat.card_congr (Quotient.congr e h)
end LeanPool.K5MinorFreeChoosability
