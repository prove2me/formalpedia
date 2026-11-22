-- Prove2me | solution 1 for Nock.BTree.size_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:10.024672+00:00
-- url     : https://prove2.me/submissions/92c67987-4346-4b44-841e-4af7bd52c5e9

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
theorem _root_.solution (t : BTree) : t.size = 2 * (toBin t).numNodes + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [size, toBin, BinaryTree.numNodes, ihl, ihr]
      omega
end Nock.BTree
