-- Prove2me | solution 1 for LeanPool.Vizing.degree_toSimpleGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:26.261983+00:00
-- url     : https://prove2.me/submissions/d6a7ddaf-c2bf-48e0-90d2-ec11324bd37a

module
public import Definitions.Def_LeanPool_Vizing_Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Definitions.Def_LeanPool_Vizing_Endpoints
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
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]
namespace LeanPool.Vizing
theorem _root_.solution {H : SimpleGraph V} [DecidableRel H.Adj]
    (Cp : H.ConnectedComponent)
    [∀ z : ↥Cp, Fintype (Cp.toSimpleGraph.neighborSet z)] (z : ↥Cp) :
    Cp.toSimpleGraph.degree z ≤ H.degree z.1 := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn (fun t => t.1) ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, mem_neighborFinset] at ht ⊢
    exact ht
  · intro t _ s _ h
    exact Subtype.ext h
end LeanPool.Vizing
