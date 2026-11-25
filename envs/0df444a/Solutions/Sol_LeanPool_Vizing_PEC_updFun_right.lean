-- Prove2me | solution 1 for LeanPool.Vizing.PEC.updFun_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:41:28.697665+00:00
-- url     : https://prove2.me/submissions/49fdcf1f-ed47-414c-aaf0-36d2f6efb227

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
theorem _root_.solution {f : V → V → Option C} {x y : V} (o : Option C) :
    updFun f x y o y x = o := if_pos (Or.inr ⟨rfl, rfl⟩)
end LeanPool.Vizing.PEC
