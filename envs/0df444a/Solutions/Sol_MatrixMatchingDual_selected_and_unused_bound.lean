-- Prove2me | solution 1 for MatrixMatchingDual.selected_and_unused_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/402f7c6f-67aa-455e-bf5e-56906a9ba0fd

import Std
import Definitions.Def_MatchingDual
import Theorems.Thm_MatrixMatchingDual_unused_sum_nonpositive
import Theorems.Thm_MatrixMatchingDual_selected_edge_bound

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution (edges : List Edge) (unused : List Int)
    (hedge : ∀ e ∈ edges, e.rowPrice+e.columnPrice ≤ e.cost)
    (hunused : ∀ p ∈ unused, p ≤ 0) :
    rowSum edges+selectedSum edges+unused.sum ≤ costSum edges := by
  have he := selected_edge_bound edges hedge
  have hu := unused_sum_nonpositive unused hunused
  omega
end MatrixMatchingDual
