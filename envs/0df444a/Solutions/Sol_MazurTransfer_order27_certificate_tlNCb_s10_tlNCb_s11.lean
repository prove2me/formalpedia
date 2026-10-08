-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s10_tlNCb_s11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:32:38.071057+00:00
-- url     : https://prove2.me/submissions/19512ef6-930a-48ef-beb8-bcf1d6f372ce

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s10
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s11

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP10c0 f ξ + tlNCbP10c1 f ξ) + (tlNCbP10c2 f ξ + tlNCbP10c3 f ξ)) +
        ((tlNCbP10c4 f ξ + tlNCbP10c5 f ξ) + (tlNCbP10c6 f ξ + tlNCbP10c7 f ξ))) +
        (((tlNCbP10c8 f ξ + tlNCbP10c9 f ξ) + (tlNCbP10c10 f ξ + tlNCbP10c11 f ξ)) +
        (tlNCbP10c12 f ξ + tlNCbP10c13 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP11c0 f ξ + tlNCbP11c1 f ξ) + (tlNCbP11c2 f ξ + tlNCbP11c3 f ξ)) +
        ((tlNCbP11c4 f ξ + tlNCbP11c5 f ξ) + (tlNCbP11c6 f ξ + tlNCbP11c7 f ξ))) +
        (((tlNCbP11c8 f ξ + tlNCbP11c9 f ξ) + (tlNCbP11c10 f ξ + tlNCbP11c11 f ξ)) +
        ((tlNCbP11c12 f ξ + tlNCbP11c13 f ξ) + tlNCbP11c14 f ξ))) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s10, MazurTransfer.order27_leaf_tlNCb_s11⟩

#print axioms solution
