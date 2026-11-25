-- Prove2me | solution 1 for LeanPool.Vizing.PEC.kempeSwapFun_isSome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:27.018021+00:00
-- url     : https://prove2.me/submissions/7d81868b-45ab-4c97-bbb0-123074a8e7ab

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



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
theorem _root_.solution (c : PEC G C) (a b : C) (x u v : V) :
    (c.kempeSwapFun a b x u v = none) ↔ (c.col u v = none) := by
  classical
  by_cases hu : (c.kempeGraph a b).Reachable x u
  · rw [kempeSwapFun_of_reachable c a b hu v]
    cases c.col u v <;> simp
  · rw [kempeSwapFun_of_not_reachable c a b hu v]
end LeanPool.Vizing.PEC
