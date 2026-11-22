-- Prove2me | solution 1 for Nock.Verb.enum_nonpending_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:02.175201+00:00
-- url     : https://prove2.me/submissions/dc0ef2c8-4622-49e4-a962-caff5b4d53c8

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
theorem _root_.solution : ∀ (v : Verb), isTerminal v = true →
    ∀ (c : Nat), ∀ p ∈ (enum v c).2, p.2.isPending = false := by
  intro v
  induction v with
  | leaf n => intro _ c p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro h c p hp
      simp only [isTerminal, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hl⟩, hr⟩ := h
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; simp [isPending, ha]
      · exact ihl hl (c + 1) p hleft
      · exact ihr hr _ p hright
end Nock.Verb
