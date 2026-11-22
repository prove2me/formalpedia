-- Prove2me | solution 1 for Nock.Verb.finite_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:33.950716+00:00
-- url     : https://prove2.me/submissions/0e3a1796-a067-4617-8b57-c7d1ab96ac1d

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_next_none_of_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution (n : Nat) : Finite (.leaf n) :=
  ⟨[.leaf n], ⟨rfl, trivial⟩, .leaf n, rfl, next_none_of_terminal rfl⟩
end Nock.Verb
