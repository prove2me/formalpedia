-- Prove2me | solution 1 for Nock.Verb.slot_three_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:51.954458+00:00
-- url     : https://prove2.me/submissions/7e196671-aa4a-4a43-814a-30301005b50e

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
theorem _root_.solution {k : Nat} : Noun.slot 3 (.atom k) = none := by simp [Noun.slot]
end Nock.Verb
