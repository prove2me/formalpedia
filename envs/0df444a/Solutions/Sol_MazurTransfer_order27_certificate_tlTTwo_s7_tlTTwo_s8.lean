-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s7_tlTTwo_s8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:45:50.252984+00:00
-- url     : https://prove2.me/submissions/3029dbc0-4813-4f1d-97b0-025725518036

import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s7
import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s8

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ) + (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ)) +
        ((tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ) + (tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ))) +
        (((tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ) + (tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ)) +
        tlTTwoP7c12 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ) + (tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ)) +
        ((tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ) + (tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ))) +
        (((tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ) + (tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ)) +
        (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ))) := by
  exact ⟨MazurTransfer.order27_leaf_tlTTwo_s7, MazurTransfer.order27_leaf_tlTTwo_s8⟩

#print axioms solution
