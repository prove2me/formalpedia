-- Prove2me | solution 1 for MatrixMatchingDual.tight_candidate_objective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/3be94a34-a8b3-453a-b705-77b5aed4b1ff

import Std
import Definitions.Def_MatchingDual
import Theorems.Thm_MatrixMatchingDual_perm_int_sum
import Theorems.Thm_MatrixMatchingDual_selected_edge_equality
import Theorems.Thm_MatrixMatchingDual_unused_sum_zero

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution (candidate : List Edge) (unused allPrices : List Int)
    (rowTotal : Int)
    (htight : ∀ e ∈ candidate, e.rowPrice+e.columnPrice = e.cost)
    (hzero : ∀ p ∈ unused, p = 0)
    (hpartition : List.Perm ((candidate.map Edge.columnPrice)++unused) allPrices)
    (hrows : rowSum candidate = rowTotal) :
      costSum candidate = rowTotal+allPrices.sum := by
  have he := selected_edge_equality candidate htight
  have hu := unused_sum_zero unused hzero
  have hsum := perm_int_sum hpartition
  rw [List.sum_append,hu] at hsum
  change selectedSum candidate+0=allPrices.sum at hsum
  omega
end MatrixMatchingDual
