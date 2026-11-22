-- Prove2me | solution 1 for Nock.Verb.replaceAux_counter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:22.672103+00:00
-- url     : https://prove2.me/submissions/54a08e1b-8e77-494f-87df-c0a465d70284

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (i : Nat) (new : Verb) : ∀ (v : Verb) (c : Nat),
    (replaceAux i new v c).1 = (enum v c).1 := by
  intro v
  induction v with
  | leaf k => intro c; simp [replaceAux, enum]
  | node a l r ihl ihr =>
      intro c
      simp only [replaceAux, enum]
      rw [ihl (c+1), ihr]
end Nock.Verb
