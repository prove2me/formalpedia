-- Prove2me | solution 1 for Nock.Noun.eq_of_shape_leafList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:12.758825+00:00
-- url     : https://prove2.me/submissions/3b0349e1-44b7-42b9-b25e-449e4109858e

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Theorems.Thm_Nock_Noun_shape_leaves_eq

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution :
    ∀ {n₁ n₂ : Noun}, n₁.shape = n₂.shape → n₁.leafList = n₂.leafList → n₁ = n₂ := by
  intro n₁
  induction n₁ with
  | atom k₁ =>
      intro n₂ hshape hleaf
      cases n₂ with
      | atom k₂ =>
          simp only [leafList, List.cons.injEq, and_true] at hleaf; rw [hleaf]
      | cell l r => simp [shape] at hshape
  | cell l₁ r₁ ihl ihr =>
      intro n₂ hshape hleaf
      cases n₂ with
      | atom k₂ => simp [shape] at hshape
      | cell l₂ r₂ =>
          simp only [shape, BTree.node.injEq] at hshape
          obtain ⟨hsl, hsr⟩ := hshape
          simp only [leafList] at hleaf
          have hlen : l₁.leafList.length = l₂.leafList.length := by
            rw [leafList_length, leafList_length, shape_leaves_eq hsl]
          obtain ⟨hll, hrl⟩ := List.append_inj hleaf hlen
          rw [ihl hsl hll, ihr hsr hrl]
end Nock.Noun
