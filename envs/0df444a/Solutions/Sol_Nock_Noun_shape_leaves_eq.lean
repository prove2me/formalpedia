-- Prove2me | solution 1 for Nock.Noun.shape_leaves_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:37.861253+00:00
-- url     : https://prove2.me/submissions/9c5e1414-3764-4b6a-a169-e0f9b21a212b

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
theorem _root_.solution {n₁ n₂ : Noun} (h : n₁.shape = n₂.shape) :
    n₁.leaves = n₂.leaves := by
  have hs : n₁.shape.size = n₂.shape.size := by rw [h]
  rw [shape_size, shape_size] at hs
  have e₁ := size_add_one n₁
  have e₂ := size_add_one n₂
  omega
end Nock.Noun
