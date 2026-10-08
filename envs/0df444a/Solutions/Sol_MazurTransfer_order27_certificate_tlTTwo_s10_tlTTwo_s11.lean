-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s10_tlTTwo_s11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:45:53.546837+00:00
-- url     : https://prove2.me/submissions/8bbfa41d-e214-4455-ad43-e910f45edaba

import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s10
import Theorems.Thm_MazurTransfer_order27_leaf_tlTTwo_s11

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) + (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ)) +
        ((tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ) + (tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ))) +
        ((tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ) + (tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c4 f ξ + tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ) + (tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ)) +
        ((tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ) + (tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ))) +
        (((tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ) + (tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ)) +
        (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ))) := by
  exact ⟨MazurTransfer.order27_leaf_tlTTwo_s10, MazurTransfer.order27_leaf_tlTTwo_s11⟩

#print axioms solution
