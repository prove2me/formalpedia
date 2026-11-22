-- Prove2me | solution 1 for Nock.Noun.noun_dyck_leaf_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:18.122015+00:00
-- url     : https://prove2.me/submissions/0e2b262b-4353-436d-bdfe-fc5d70186d82

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Theorems.Thm_Nock_Noun_eq_of_shape_leafList

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution :
    Function.Injective (fun n : Noun => (n.dyckWord, n.leafList)) := by
  intro n₁ n₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hd, hl⟩ := h
  have hshape : n₁.shape = n₂.shape :=
    BTree.encode_injective (by simpa only [dyckWord] using hd)
  exact eq_of_shape_leafList hshape hl
end Nock.Noun
