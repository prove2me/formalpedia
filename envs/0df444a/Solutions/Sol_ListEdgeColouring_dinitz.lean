-- Prove2me | solution 1 for ListEdgeColouring.dinitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:25.090541+00:00
-- url     : https://prove2.me/submissions/d807c101-4bde-45ae-ae83-0cb7055236ef

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_GalvinMultigraph
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinDinitzSolution
public import Theorems.Thm_Galvin_dinitz


set_option autoImplicit true
@[expose] public section
public section
open ListEdgeColouring
namespace ListEdgeColouring
theorem _root_.solution {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) :=
  Galvin.dinitz n lists hLists
end ListEdgeColouring
