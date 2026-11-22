-- Prove2me | solution 1 for Nock.Verb.strictSelect_dfs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:08.13382+00:00
-- url     : https://prove2.me/submissions/785be20b-72b5-4700-96fb-5ee9d576f6d3

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
theorem _root_.solution : StrictSelect dfsLt where
  irrefl i := Nat.lt_irrefl i
  trans h h' := Nat.lt_trans h h'
  total hne := Nat.lt_or_gt_of_ne hne
end Nock.Verb
