-- Prove2me | solution 1 for Nock.Verb.slot_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:46.240272+00:00
-- url     : https://prove2.me/submissions/f4454ef9-4133-43e1-a0f0-382e4fff552d

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
theorem _root_.solution {a b : Noun} : Noun.slot 3 (.cell a b) = some b := by simp [Noun.slot]
end Nock.Verb
