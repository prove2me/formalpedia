-- Prove2me | solution 1 for Konig.lineGraph_colorable_of_colorable_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:49:16.902798+00:00
-- url     : https://prove2.me/submissions/4169088f-dec9-4111-aa9f-0062a75dfccc

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
public import Theorems.Thm_Konig_exists_total_of_bipartite
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
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
namespace Konig
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.Colorable 2) : G.lineGraph.Colorable G.maxDegree := by
  classical
  obtain ⟨s⟩ := h
  obtain ⟨c, hc⟩ := exists_total_of_bipartite (C := Fin G.maxDegree) s (by simp)
  exact ⟨c.lineGraphColoring hc⟩
end Konig
