-- Prove2me | solution 1 for LeanPool.Vizing.lineGraph_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:19.641676+00:00
-- url     : https://prove2.me/submissions/60ab08dc-c8d8-4c49-ab29-d6676c363c7f

module
public import Definitions.Def_LeanPool_Vizing_Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_LeanPool_Vizing_Main
public import Theorems.Thm_LeanPool_Vizing_PEC_exists_total
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
namespace LeanPool.Vizing
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.lineGraph).Colorable (G.maxDegree + 1) := by
  classical
  obtain ⟨c, hc⟩ := PEC.exists_total (G := G) (C := Fin (G.maxDegree + 1))
    (by simp)
  exact ⟨c.lineGraphColoring hc⟩
end LeanPool.Vizing
