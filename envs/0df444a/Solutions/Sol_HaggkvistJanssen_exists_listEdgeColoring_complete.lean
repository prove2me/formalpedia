-- Prove2me | solution 1 for HaggkvistJanssen.exists_listEdgeColoring_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:08.337812+00:00
-- url     : https://prove2.me/submissions/80951051-a896-410e-96fc-3e5276fc739b

module
public import Mathlib
public import Definitions.Def_LeanPool_ListEdgeColoringComplete
public import Definitions.Def_HaggkvistJanssen_Solution
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_exists_listEdgeColoring_complete


set_option autoImplicit true
@[expose] public section
public section
open HaggkvistJanssen
namespace HaggkvistJanssen
theorem _root_.solution {V Color : Type*} [Fintype V]
    (lists : (⊤ : SimpleGraph V).edgeSet → Finset Color)
    (hLists : ∀ e, Fintype.card V ≤ (lists e).card) :
    ∃ coloring : (⊤ : SimpleGraph V).lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e :=
  LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete lists hLists
end HaggkvistJanssen
