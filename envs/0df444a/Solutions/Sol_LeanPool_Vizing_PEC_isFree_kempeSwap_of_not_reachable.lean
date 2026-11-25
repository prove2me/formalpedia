-- Prove2me | solution 1 for LeanPool.Vizing.PEC.isFree_kempeSwap_of_not_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:58:07.223345+00:00
-- url     : https://prove2.me/submissions/3147bfe2-8c9a-4383-b6c9-3444f9eafa0b

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right


attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V]
namespace LeanPool.Vizing.PEC
theorem _root_.solution (c : PEC G C) (a b : C) {x v : V}
    (hv : ¬ (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v γ := by
  constructor
  · intro h u hu
    exact h u (by rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hv u]; exact hu)
  · intro h u hu
    rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hv u] at hu
    exact h u hu
end LeanPool.Vizing.PEC
