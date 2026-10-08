-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s14_tlNCb_s15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:33:58.139734+00:00
-- url     : https://prove2.me/submissions/a6731c03-05ed-4d1a-aa94-4134a4f248a3

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s14
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s15

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP14c0 f ξ + tlNCbP14c1 f ξ) + (tlNCbP14c2 f ξ + tlNCbP14c3 f ξ)) +
        ((tlNCbP14c4 f ξ + tlNCbP14c5 f ξ) + (tlNCbP14c6 f ξ + tlNCbP14c7 f ξ))) +
        (((tlNCbP14c8 f ξ + tlNCbP14c9 f ξ) + (tlNCbP14c10 f ξ + tlNCbP14c11 f ξ)) +
        ((tlNCbP14c12 f ξ + tlNCbP14c13 f ξ) + (tlNCbP14c14 f ξ + tlNCbP14c15 f ξ)))) +
        (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) +
        ((tlNCbP15c4 f ξ + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ))) +
        (((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) +
        ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ)))) +
        ((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + tlNCbP15c18 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s14, MazurTransfer.order27_leaf_tlNCb_s15⟩

#print axioms solution
