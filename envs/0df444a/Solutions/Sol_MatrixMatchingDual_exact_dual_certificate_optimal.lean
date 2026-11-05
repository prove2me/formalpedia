-- Prove2me | solution 1 for MatrixMatchingDual.exact_dual_certificate_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/f2ab54c8-cdeb-400d-92ff-249bd92fb8a0

import Std
import Definitions.Def_MatchingDual
import Theorems.Thm_MatrixMatchingDual_matching_weak_duality

set_option autoImplicit true
open MatrixMatchingDual
namespace MatrixMatchingDual
theorem _root_.solution (candidateCost rowTotal : Int)
    (allPrices : List Int) (hcertificate : candidateCost = rowTotal+allPrices.sum)
    (alternative : List Edge) (unused : List Int)
    (hedge : ∀ e ∈ alternative, e.rowPrice+e.columnPrice ≤ e.cost)
    (hunused : ∀ p ∈ unused, p ≤ 0)
    (hpartition : List.Perm ((alternative.map Edge.columnPrice)++unused) allPrices)
    (hrows : rowSum alternative = rowTotal) :
    candidateCost ≤ costSum alternative := by
  rw [hcertificate]
  exact matching_weak_duality alternative unused allPrices rowTotal hedge hunused hpartition hrows
end MatrixMatchingDual
