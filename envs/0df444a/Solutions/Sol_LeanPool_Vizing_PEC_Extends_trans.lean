-- Prove2me | solution 1 for LeanPool.Vizing.PEC.Extends.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:41:40.61581+00:00
-- url     : https://prove2.me/submissions/8bf19679-830a-4d9c-9a83-ce321aa2dcb2

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
omit [DecidableEq V]
namespace LeanPool.Vizing.PEC
namespace Extends
theorem _root_.solution {c₁ c₂ c₃ : PEC G C} (h₁ : Extends c₁ c₂) (h₂ : Extends c₂ c₃) :
    Extends c₁ c₃ := fun u v h => h₂ u v (h₁ u v h)
end Extends
end LeanPool.Vizing.PEC
