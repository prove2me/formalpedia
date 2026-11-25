-- Prove2me | solution 1 for LeanPool.Vizing.PEC.extends_kempeSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:43.501486+00:00
-- url     : https://prove2.me/submissions/0a9f6012-f03e-4499-9eac-8d93d6677072

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwapFun_isSome
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
theorem _root_.solution (c : PEC G C) (a b : C) (x : V) : Extends c (c.kempeSwap a b x) := by
  intro u v h
  rw [kempeSwap_col, ne_eq, kempeSwapFun_isSome]
  exact h
end LeanPool.Vizing.PEC
