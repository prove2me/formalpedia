-- Prove2me | solution 1 for LeanPool.Vizing.PEC.setEdge_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:38:13.910699+00:00
-- url     : https://prove2.me/submissions/ebff0d01-9a50-48a5-9791-e2bbfb140e95

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic

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
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) :
    (c.setEdge γ hadj hx hy).col = updFun c.col x y (some γ) := rfl
end LeanPool.Vizing.PEC
