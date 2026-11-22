-- Prove2me | solution 1 for Nock.Verb.terminal_of_enum_nonpending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:07.212353+00:00
-- url     : https://prove2.me/submissions/8ea8dcfe-259a-471c-be6e-fb9d8e3aa9c4

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution :
    ∀ (v : Verb) (c : Nat),
      (∀ p ∈ (enum v c).2, p.2.isPending = false) → isTerminal v = true := by
  intro v
  induction v with
  | leaf k => intro c _; rfl
  | node a l r ihl ihr =>
      intro c h
      have hroot : ((c, Verb.node a l r) : Nat × Verb) ∈ (enum (Verb.node a l r) c).2 := by
        simp [enum]
      have hpc := h _ hroot
      have ha : a.isNull = true := by
        simp only [isPending] at hpc
        cases hh : a.isNull with
        | true => rfl
        | false => rw [hh] at hpc; simp at hpc
      have hl : isTerminal l = true := by
        apply ihl (c + 1)
        intro p hp
        apply h
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hp)
      have hr : isTerminal r = true := by
        apply ihr (enum l (c + 1)).1
        intro p hp
        apply h
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hp)
      simp only [isTerminal, ha, hl, hr, Bool.and_self]
end Nock.Verb
