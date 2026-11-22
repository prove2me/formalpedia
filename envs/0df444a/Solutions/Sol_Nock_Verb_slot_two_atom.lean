-- Prove2me | solution 1 for Nock.Verb.slot_two_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:51.544798+00:00
-- url     : https://prove2.me/submissions/1042b14c-832c-4286-a547-86c6cd9b64a2

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
theorem _root_.solution {k : Nat} : Noun.slot 2 (.atom k) = none := by simp [Noun.slot]
end Nock.Verb
