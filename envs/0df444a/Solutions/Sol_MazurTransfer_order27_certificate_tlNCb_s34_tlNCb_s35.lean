-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s34_tlNCb_s35
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:40:54.888998+00:00
-- url     : https://prove2.me/submissions/a136a49b-93ea-427c-af86-5e29973473c9

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s34
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s35

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ)) +
        ((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ))) +
        (((tlNCbP34c8 f ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ)) +
        ((tlNCbP34c12 f ξ + tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)))) +
        (tlNCbP34c16 f ξ + tlNCbP34c17 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP35c0 f ξ + tlNCbP35c1 f ξ) + (tlNCbP35c2 f ξ + tlNCbP35c3 f ξ)) +
        ((tlNCbP35c4 f ξ + tlNCbP35c5 f ξ) + (tlNCbP35c6 f ξ + tlNCbP35c7 f ξ))) +
        (((tlNCbP35c8 f ξ + tlNCbP35c9 f ξ) + (tlNCbP35c10 f ξ + tlNCbP35c11 f ξ)) +
        ((tlNCbP35c12 f ξ + tlNCbP35c13 f ξ) + (tlNCbP35c14 f ξ + tlNCbP35c15 f ξ)))) +
        (tlNCbP35c16 f ξ + tlNCbP35c17 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s34, MazurTransfer.order27_leaf_tlNCb_s35⟩

#print axioms solution
