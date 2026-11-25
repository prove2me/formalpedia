-- Prove2me | solution 1 for LeanPool.Vizing.PEC.setEdge_col_of_ne_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:56:36.393614+00:00
-- url     : https://prove2.me/submissions/09985c2f-7ca4-4b2c-9e4a-0439973f3b33

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_of_ne

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
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (u : V) :
    (c.setEdge γ hadj hx hy).col w u = c.col w u :=
  updFun_of_ne _ (by tauto)
end LeanPool.Vizing.PEC
