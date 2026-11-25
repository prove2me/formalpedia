-- Prove2me | solution 1 for LeanPool.Vizing.PEC.isFree_kempeSwap_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:58:03.723299+00:00
-- url     : https://prove2.me/submissions/05b0a596-cec1-4f9d-9ee6-f1ab96e22603

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
    (hv : (c.kempeGraph a b).Reachable x v) (γ : C) :
    (c.kempeSwap a b x).IsFree v γ ↔ c.IsFree v (Equiv.swap a b γ) := by
  constructor
  · intro h u hu
    refine h u ?_
    rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hv u, hu]
    simp
  · intro h u hu
    rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hv u] at hu
    cases hc : c.col v u with
    | none => rw [hc] at hu; simp at hu
    | some δ =>
      rw [hc] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      refine h u ?_
      rw [hc, ← hu]
      simp
end LeanPool.Vizing.PEC
