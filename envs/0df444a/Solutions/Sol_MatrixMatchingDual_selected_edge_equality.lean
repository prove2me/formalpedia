-- Prove2me | solution 1 for MatrixMatchingDual.selected_edge_equality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/914dff70-574d-4063-b60e-27c012d84f2c

import Std
import Definitions.Def_MatchingDual

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution (edges : List Edge)
    (h : ∀ e ∈ edges, e.rowPrice+e.columnPrice = e.cost) :
    rowSum edges+selectedSum edges = costSum edges := by
  induction edges with
  | nil => simp [rowSum,selectedSum,costSum]
  | cons e es ih =>
    have he := h e (by simp)
    have hrest : ∀ f ∈ es, f.rowPrice+f.columnPrice = f.cost := by
      intro f hf
      exact h f (by simp [hf])
    have hs := ih hrest
    simp only [rowSum,selectedSum,costSum,List.map_cons,List.sum_cons] at *
    omega
end MatrixMatchingDual
