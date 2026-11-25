-- Prove2me | solution 1 for LeanPool.Vizing.PEC.mem_uncoloured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:05:04.411836+00:00
-- url     : https://prove2.me/submissions/0ae4ec32-3586-4ef0-90d9-a97ddbd498d9

module
public import Definitions.Def_LeanPool_Vizing_Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_LeanPool_Vizing_Main
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [Fintype C] [DecidableEq C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution [DecidableRel G.Adj] (c : PEC G C) (p : V × V) :
    p ∈ c.uncoloured ↔ G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none := by
  classical
  simp [uncoloured]
end LeanPool.Vizing.PEC
