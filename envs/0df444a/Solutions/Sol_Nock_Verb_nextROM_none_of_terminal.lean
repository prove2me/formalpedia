-- Prove2me | solution 1 for Nock.Verb.nextROM_none_of_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:06.554128+00:00
-- url     : https://prove2.me/submissions/f55445a3-6fec-4b68-b12c-4b3511ea1bd8

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
theorem _root_.solution {v : Verb} (h : isTerminal v = true) : nextROM v = none := by
  unfold nextROM; rw [getIndex_none_of_terminal h]
end Nock.Verb
