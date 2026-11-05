-- Prove2me | solution 1 for MatrixMatchingDual.matching_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/0cfa8cc0-884c-4945-9eb1-2dbe7bf7fac0

import Std
import Definitions.Def_MatchingDual
import Theorems.Thm_MatrixMatchingDual_perm_int_sum
import Theorems.Thm_MatrixMatchingDual_selected_and_unused_bound

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution (edges : List Edge) (unused allPrices : List Int)
    (rowTotal : Int)
    (hedge : ∀ e ∈ edges, e.rowPrice+e.columnPrice ≤ e.cost)
    (hunused : ∀ p ∈ unused, p ≤ 0)
    (hpartition : List.Perm ((edges.map Edge.columnPrice)++unused) allPrices)
    (hrows : rowSum edges = rowTotal) :
    rowTotal+allPrices.sum ≤ costSum edges := by
  have hsum := perm_int_sum hpartition
  rw [List.sum_append] at hsum
  have he := selected_and_unused_bound edges unused hedge hunused
  unfold selectedSum at he
  rw [hrows] at he
  omega
end MatrixMatchingDual
