-- Prove2me | solution 1 for Nock.BTree.dyck_length_graded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:17.703216+00:00
-- url     : https://prove2.me/submissions/f179ae85-2715-49b2-9ece-7d195563b631

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
theorem _root_.solution {w : List Bool} (t : BTree) (ht : encode t = w) (lam : Nat) :
    w.length = 2 * lam ↔ t.size = 2 * lam + 1 := by
  have := encode_length_add_one t
  rw [ht] at this
  omega
end Nock.BTree
