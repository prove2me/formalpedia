-- Prove2me | solution 1 for LeanPool.Vizing.PEC.updFun_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:52:22.271995+00:00
-- url     : https://prove2.me/submissions/1b117f4e-da54-4d53-95bf-2e9cf847d120

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
theorem _root_.solution {f : V → V → Option C} {x y u v : V} (o : Option C)
    (h : ¬((u = x ∧ v = y) ∨ (u = y ∧ v = x))) : updFun f x y o u v = f u v := if_neg h
end LeanPool.Vizing.PEC
