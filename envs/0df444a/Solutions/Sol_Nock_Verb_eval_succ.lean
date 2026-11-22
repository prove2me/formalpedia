-- Prove2me | solution 1 for Nock.Verb.eval_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:01.170797+00:00
-- url     : https://prove2.me/submissions/f0358763-9065-41db-9679-e10de3c9d0ae

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
theorem _root_.solution (n : Nat) (v : Verb) :
    eval (n + 1) v = match next v with | some v' => eval n v' | none => haltOutcome v := rfl
end Nock.Verb
