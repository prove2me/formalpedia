-- Prove2me | solution 1 for LeanPool.Vizing.PEC.updFun_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:38:03.169979+00:00
-- url     : https://prove2.me/submissions/f6bd6774-74d2-47fc-83a0-87804f17758d

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
    updFun f x y o x y = o := if_pos (Or.inl ⟨rfl, rfl⟩)
end LeanPool.Vizing.PEC
