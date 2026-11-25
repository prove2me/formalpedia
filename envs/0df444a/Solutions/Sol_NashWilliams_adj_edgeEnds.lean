-- Prove2me | solution 1 for NashWilliams.adj_edgeEnds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:44.54345+00:00
-- url     : https://prove2.me/submissions/8a000217-a605-45f1-bcec-898ec8e9d405

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_mk_edgeEnds

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution (e : G.edgeSet) : G.Adj (edgeEnds G e).1 (edgeEnds G e).2 := by
  have h := e.2
  rwa [← mk_edgeEnds G e, SimpleGraph.mem_edgeSet] at h
end NashWilliams
