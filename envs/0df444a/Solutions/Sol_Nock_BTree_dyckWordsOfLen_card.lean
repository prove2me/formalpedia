-- Prove2me | solution 1 for Nock.BTree.dyckWordsOfLen_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:21.24995+00:00
-- url     : https://prove2.me/submissions/297de26d-6771-47d8-9711-089a62312f2c

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
theorem _root_.solution (lam : ℕ) : (dyckWordsOfLen lam).card = catalan lam := by
  rw [dyckWordsOfLen, Finset.card_map, BinaryTree.treesOfNumNodesEq_card_eq_catalan]
end Nock.BTree
