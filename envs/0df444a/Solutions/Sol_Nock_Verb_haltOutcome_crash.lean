-- Prove2me | solution 1 for Nock.Verb.haltOutcome_crash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:13.795963+00:00
-- url     : https://prove2.me/submissions/e1077f8d-baef-4136-853d-5d1d148ad0b3

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
theorem _root_.solution {v : Verb} (h : v.isTerminal = false) : haltOutcome v = .crash := by
  simp [haltOutcome, h]
end Nock.Verb
