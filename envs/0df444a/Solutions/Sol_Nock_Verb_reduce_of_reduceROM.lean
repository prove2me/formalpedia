-- Prove2me | solution 1 for Nock.Verb.reduce_of_reduceROM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:15.477707+00:00
-- url     : https://prove2.me/submissions/5c025a68-d35f-45a5-b734-557ec6b78fe1

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
theorem _root_.solution {v r : Verb} (h : reduceROM v = some r) : reduce v = some r := by
  unfold reduceROM at h
  split at h <;> first | exact h | simp at h
end Nock.Verb
