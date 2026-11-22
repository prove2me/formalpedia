-- Prove2me | solution 1 for Nock.Noun.dyckWord_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:33.277024+00:00
-- url     : https://prove2.me/submissions/20702e1f-0b8a-4778-96aa-c50b5796d4a7

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Theorems.Thm_Nock_Noun_shape_size
public import Theorems.Thm_Nock_Noun_size_add_one


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n : Noun) : n.dyckWord.length + 2 = 2 * n.leaves := by
  have h1 := Nock.BTree.encode_length_add_one n.shape
  have h2 := shape_size n
  have h3 := size_add_one n
  simp only [dyckWord]
  omega
end Nock.Noun
