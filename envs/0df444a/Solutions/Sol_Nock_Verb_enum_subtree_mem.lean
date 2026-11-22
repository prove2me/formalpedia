-- Prove2me | solution 1 for Nock.Verb.enum_subtree_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:11.835812+00:00
-- url     : https://prove2.me/submissions/d9ba050f-6b9d-4f1e-9104-99016f837bea

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
    ∀ (v : Verb) (c i : Nat) (sub : Verb),
      (i, sub) ∈ (enum v c).2 → ∀ p ∈ (enum sub i).2, p ∈ (enum v c).2 := by
  intro v
  induction v with
  | leaf k => intro c i sub hmem; simp [enum] at hmem
  | node a l r ihl ihr =>
      intro c i sub hmem p hp
      simp only [enum, List.mem_cons, List.mem_append] at hmem
      rcases hmem with hroot | hleft | hright
      · simp only [Prod.mk.injEq] at hroot
        obtain ⟨rfl, rfl⟩ := hroot
        simpa only [enum] using hp
      · have := ihl (c + 1) i sub hleft p hp
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl this)
      · have := ihr (enum l (c + 1)).1 i sub hright p hp
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr this)
end Nock.Verb
