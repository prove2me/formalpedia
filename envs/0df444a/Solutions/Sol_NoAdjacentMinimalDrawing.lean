-- Prove2me | solution 1 for NoAdjacentMinimalDrawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T21:04:10.855993+00:00
-- url     : https://prove2.me/submissions/0465d0c2-9f6e-4d36-b333-67f23cc27550
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AdjacentEdgeTailFreeReroute
import Definitions.Def_CrossingNumber
import Theorems.Thm_NatSInfRangeAttained
import Theorems.Thm_OrdinaryPolygonalDrawingNonempty

open Classical
noncomputable section

-- Full upstream proof body from Tablet/NoAdjacentMinimalDrawing.lean, with only the target wrapper/module layout adapted.
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    ∃ D : OrdinaryPolygonalDrawing G,
      D.crossingSet.card = CrossingNumber G ∧ D.adjacentEdgeCrossingCount = 0 := by
  have hnonempty : Nonempty (OrdinaryPolygonalDrawing G) :=
    OrdinaryPolygonalDrawingNonempty G
  have hattainment :
      ∃ D : OrdinaryPolygonalDrawing G,
        D.crossingSet.card = CrossingNumber G ∧
          ∀ E : OrdinaryPolygonalDrawing G,
            CrossingNumber G ≤ E.crossingSet.card := by
    simpa [CrossingNumber] using
      (NatSInfRangeAttained
        (α := OrdinaryPolygonalDrawing G)
        (fun E : OrdinaryPolygonalDrawing G => E.crossingSet.card)
        hnonempty)
  rcases hattainment with ⟨D, ⟨hDmin, hminimal⟩⟩
  refine ⟨D, hDmin, ?_⟩
  by_contra hadj
  rw [D.adjacentEdgeCrossingCount_eq] at hadj
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hadj
  rw [Finset.mem_filter] at hx
  rcases hx with ⟨hxCross, alpha, beta, hab, ⟨u, hua, hub⟩, hxa, hxb⟩
  obtain ⟨D', hdecrease⟩ :=
    AdjacentEdgeTailFreeReroute G D alpha beta u hab hua hub
      ⟨x, hxCross, hxa, hxb⟩
  have hlower := hminimal D'
  omega
