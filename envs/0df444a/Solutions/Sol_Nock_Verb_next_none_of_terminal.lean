-- Prove2me | solution 1 for Nock.Verb.next_none_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:53.927034+00:00
-- url     : https://prove2.me/submissions/34c3e28d-b92d-47c8-bea8-37293530194c

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_getIndex_none_of_terminal

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {v : Verb} (h : isTerminal v = true) : next v = none := by
  unfold next; rw [getIndex_none_of_terminal h]
end Nock.Verb
