-- Prove2me | solution 1 for Nock.BTree.dyck_iff_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:19.520458+00:00
-- url     : https://prove2.me/submissions/0554ba28-41b8-4e2f-8a21-e52d5e3d82a1

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Theorems.Thm_Nock_BTree_dyck_encode
public import Theorems.Thm_Nock_BTree_exists_encode_of_dyck

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.BTree
namespace Nock.BTree
theorem _root_.solution {w : List Bool} : Dyck w ↔ ∃ t : BTree, encode t = w :=
  ⟨exists_encode_of_dyck, fun ⟨t, ht⟩ => ht ▸ dyck_encode t⟩
end Nock.BTree
