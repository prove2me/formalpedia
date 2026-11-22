-- Prove2me | solution 1 for Nock.Verb.slot_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:09.584507+00:00
-- url     : https://prove2.me/submissions/03e96ac6-4035-4335-9104-314810685189

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
theorem _root_.solution {n : Noun} : Noun.slot 1 n = some n := by simp [Noun.slot]
end Nock.Verb
