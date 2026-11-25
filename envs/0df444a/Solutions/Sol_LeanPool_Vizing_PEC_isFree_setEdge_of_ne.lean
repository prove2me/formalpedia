-- Prove2me | solution 1 for LeanPool.Vizing.PEC.isFree_setEdge_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:09.671498+00:00
-- url     : https://prove2.me/submissions/f87363e8-698a-41eb-b9d4-8b5411c55fca

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_Vizing_Basic
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col_of_ne_left

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
    (hx : c.IsFree x γ) (hy : c.IsFree y γ) {w : V} (hwx : w ≠ x) (hwy : w ≠ y) (δ : C) :
    (c.setEdge γ hadj hx hy).IsFree w δ ↔ c.IsFree w δ := by
  constructor <;> intro h u hu
  · exact h u (by rw [c.setEdge_col_of_ne_left γ hadj hx hy hwx hwy u]; exact hu)
  · rw [c.setEdge_col_of_ne_left γ hadj hx hy hwx hwy u] at hu
    exact h u hu
end LeanPool.Vizing.PEC
