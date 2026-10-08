-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s22_tlNCb_s23
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:36:38.406888+00:00
-- url     : https://prove2.me/submissions/953dcd28-f7cb-4bd8-a325-ae4c811e83fd

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s22
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s23

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP22c0 f ξ + tlNCbP22c1 f ξ) + (tlNCbP22c2 f ξ + tlNCbP22c3 f ξ)) +
        ((tlNCbP22c4 f ξ + tlNCbP22c5 f ξ) + (tlNCbP22c6 f ξ + tlNCbP22c7 f ξ))) +
        (((tlNCbP22c8 f ξ + tlNCbP22c9 f ξ) + (tlNCbP22c10 f ξ + tlNCbP22c11 f ξ)) +
        ((tlNCbP22c12 f ξ + tlNCbP22c13 f ξ) + (tlNCbP22c14 f ξ + tlNCbP22c15 f ξ))))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP23c0 f ξ + tlNCbP23c1 f ξ) + (tlNCbP23c2 f ξ + tlNCbP23c3 f ξ)) +
        ((tlNCbP23c4 f ξ + tlNCbP23c5 f ξ) + (tlNCbP23c6 f ξ + tlNCbP23c7 f ξ))) +
        (((tlNCbP23c8 f ξ + tlNCbP23c9 f ξ) + (tlNCbP23c10 f ξ + tlNCbP23c11 f ξ)) +
        ((tlNCbP23c12 f ξ + tlNCbP23c13 f ξ) + (tlNCbP23c14 f ξ + tlNCbP23c15 f ξ)))) +
        tlNCbP23c16 f ξ) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s22, MazurTransfer.order27_leaf_tlNCb_s23⟩

#print axioms solution
