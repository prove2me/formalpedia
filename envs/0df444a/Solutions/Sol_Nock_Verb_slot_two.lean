-- Prove2me | solution 1 for Nock.Verb.slot_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:15.680807+00:00
-- url     : https://prove2.me/submissions/b9248da7-4a33-4215-ba98-44cacb169eae

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
theorem _root_.solution {a b : Noun} : Noun.slot 2 (.cell a b) = some a := by simp [Noun.slot]
end Nock.Verb
