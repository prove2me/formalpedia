-- Prove2me | solution 1 for Nock.BTree.dyck_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:14.211364+00:00
-- url     : https://prove2.me/submissions/4c96a46a-03f9-4943-93fa-2116f176c135

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree
namespace Nock.BTree
theorem _root_.solution (t : BTree) : Dyck (encode t) := by
  induction t with
  | leaf => exact Dyck.eps
  | node l r ihl ihr => exact Dyck.cat ihl ihr
end Nock.BTree
