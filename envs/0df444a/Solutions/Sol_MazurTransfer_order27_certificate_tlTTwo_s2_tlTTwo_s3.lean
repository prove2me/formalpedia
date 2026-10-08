-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s2_tlTTwo_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:43:44.275891+00:00
-- url     : https://prove2.me/submissions/2048591e-be88-4731-a52b-c018c6d220a9

import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s2
import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s3

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c6 f ξ + tlNSqP0c7 f ξ + tlNSqP0c8 f ξ + tlNSqP1c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ) + (tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ)) +
        ((tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ) + (tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ))) +
        (((tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ) + (tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ)) +
        ((tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ) + (tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ))))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c1 f ξ + tlNSqP1c2 f ξ + tlNSqP1c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ) + (tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ)) +
        ((tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) + (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ))) +
        ((tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ) + (tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ))) := by
  exact ⟨MazurTransfer.order27_leaf_tlTTwo_s2, MazurTransfer.order27_leaf_tlTTwo_s3⟩

#print axioms solution
