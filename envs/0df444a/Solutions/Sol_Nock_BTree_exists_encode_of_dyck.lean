-- Prove2me | solution 1 for Nock.BTree.exists_encode_of_dyck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:14.725869+00:00
-- url     : https://prove2.me/submissions/5e91f31e-8494-451c-a24c-e782fbf1210b

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
theorem _root_.solution {w : List Bool} (h : Dyck w) : ∃ t : BTree, encode t = w := by
  induction h with
  | eps => exact ⟨.leaf, rfl⟩
  | @cat w₁ w₂ _ _ ih₁ ih₂ =>
      obtain ⟨t₁, ht₁⟩ := ih₁
      obtain ⟨t₂, ht₂⟩ := ih₂
      exact ⟨.node t₁ t₂, by simp only [encode, ht₁, ht₂]⟩
end Nock.BTree
