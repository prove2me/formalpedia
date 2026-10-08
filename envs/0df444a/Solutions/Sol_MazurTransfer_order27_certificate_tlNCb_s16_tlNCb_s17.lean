-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s16_tlNCb_s17
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:43.247342+00:00
-- url     : https://prove2.me/submissions/48d76ebc-9c59-4c73-9976-111cd5fb49a9

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s16
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s17

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP16c0 f ξ + tlNCbP16c1 f ξ) + (tlNCbP16c2 f ξ + tlNCbP16c3 f ξ)) +
        ((tlNCbP16c4 f ξ + tlNCbP16c5 f ξ) + (tlNCbP16c6 f ξ + tlNCbP16c7 f ξ))) +
        (((tlNCbP16c8 f ξ + tlNCbP16c9 f ξ) + (tlNCbP16c10 f ξ + tlNCbP16c11 f ξ)) +
        ((tlNCbP16c12 f ξ + tlNCbP16c13 f ξ) + (tlNCbP16c14 f ξ + tlNCbP16c15 f ξ)))) +
        ((tlNCbP16c16 f ξ + tlNCbP16c17 f ξ) + tlNCbP16c18 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP17c0 f ξ + tlNCbP17c1 f ξ) + (tlNCbP17c2 f ξ + tlNCbP17c3 f ξ)) +
        ((tlNCbP17c4 f ξ + tlNCbP17c5 f ξ) + (tlNCbP17c6 f ξ + tlNCbP17c7 f ξ))) +
        (((tlNCbP17c8 f ξ + tlNCbP17c9 f ξ) + (tlNCbP17c10 f ξ + tlNCbP17c11 f ξ)) +
        ((tlNCbP17c12 f ξ + tlNCbP17c13 f ξ) + (tlNCbP17c14 f ξ + tlNCbP17c15 f ξ)))) +
        ((tlNCbP17c16 f ξ + tlNCbP17c17 f ξ) + tlNCbP17c18 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s16, MazurTransfer.order27_leaf_tlNCb_s17⟩

#print axioms solution
