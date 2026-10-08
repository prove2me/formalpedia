-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s4_tlTTwo_s5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:43:02.181387+00:00
-- url     : https://prove2.me/submissions/2599e003-7b76-4c86-89a3-43066b61c0a7

import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s4
import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s5

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ) + (tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ)) +
        ((tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ) + (tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ))) +
        (((tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ) + (tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ)) +
        (tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ) + (tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ)) +
        ((tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ) + (tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ))) +
        (((tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ) + (tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ)) +
        (tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ))) := by
  exact ⟨MazurTransfer.order27_leaf_tlTTwo_s4, MazurTransfer.order27_leaf_tlTTwo_s5⟩

#print axioms solution
