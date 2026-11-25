-- Prove2me | solution 1 for ListEdgeColouring.galvin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:33:11.763715+00:00
-- url     : https://prove2.me/submissions/0ee52975-7da1-4b1f-a13e-e958a4a0e09e

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_GalvinMultigraph
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinDinitzSolution
public import Theorems.Thm_GalvinMultigraph_galvin
public import Theorems.Thm_Galvin_galvin


set_option autoImplicit true
@[expose] public section
public section
open ListEdgeColouring
namespace ListEdgeColouring
theorem _root_.solution {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e :=
  Galvin.galvin G hG lists hLists
end ListEdgeColouring
