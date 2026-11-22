-- Prove2me | solution 1 for Nock.Verb.isPending_replaceAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:06.332415+00:00
-- url     : https://prove2.me/submissions/5668a790-1527-467d-8c63-c1f235803f5d

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
theorem _root_.solution (i : Nat) (r₀ : Verb) : ∀ (v : Verb) (c : Nat), c ≠ i →
    Verb.isPending (replaceAux i r₀ v c).2 = Verb.isPending v := by
  intro v c hci; cases v with
  | leaf => simp [replaceAux, Verb.isPending]
  | node a l r => simp [replaceAux, if_neg hci, Verb.isPending]
end Nock.Verb
