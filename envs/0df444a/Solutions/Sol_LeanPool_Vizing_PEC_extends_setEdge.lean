-- Prove2me | solution 1 for LeanPool.Vizing.PEC.extends_setEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:55:20.344898+00:00
-- url     : https://prove2.me/submissions/8f746d59-81d3-4184-b808-647d87486ec0

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
variable {V : Type*} [DecidableEq V] {C : Type*}
open LeanPool.Vizing.PEC
variable {G : SimpleGraph V}
namespace LeanPool.Vizing.PEC
theorem _root_.solution (c : PEC G C) {x y : V} (γ : C) (hadj : G.Adj x y)
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) : Extends c (c.setEdge γ hadj hx hy) := by
  intro u v h
  simp only [setEdge_col, updFun]
  split
  · exact Option.some_ne_none _
  · exact h
end LeanPool.Vizing.PEC
