-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.mul_numClasses_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:20:05.749932+00:00
-- url     : https://prove2.me/submissions/2a128859-0d10-451f-8c4a-df8a61beb7db

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
theorem _root_.solution [Finite α] (s : Setoid α) (k : ℕ)
    (hk : ∀ a, k ≤ Nat.card {b // s a b}) : k * numClasses s ≤ Nat.card α := by
  classical
  have := Fintype.ofFinite α
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := Quotient.mk s) (s := (Finset.univ : Finset α)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hfib : ∀ q : Quotient s, k ≤ (Finset.univ.filter fun a => Quotient.mk s a = q).card := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
    refine le_trans (hk a) ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact Quotient.sound (s.symm hb)
  have : ∑ q : Quotient s, k ≤ ∑ q : Quotient s,
      (Finset.univ.filter fun a => Quotient.mk s a = q).card :=
    Finset.sum_le_sum fun q _ => hfib q
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  simp only [numClasses, Nat.card_eq_fintype_card]
  rw [Finset.card_univ] at hsum
  rw [mul_comm]
  omega
end LeanPool.K5MinorFreeChoosability
