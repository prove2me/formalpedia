-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s0_tlTTwo_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:40:13.202198+00:00
-- url     : https://prove2.me/submissions/c2282ed5-b437-4b30-a66e-2d3b108b9614

import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s0
import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s1

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlTTwo_s0, MazurTransfer.order27_leaf_tlTTwo_s1⟩

#print axioms solution
