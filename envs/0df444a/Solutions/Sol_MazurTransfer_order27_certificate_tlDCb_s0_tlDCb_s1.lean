-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlDCb_s0_tlDCb_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:43:25.483105+00:00
-- url     : https://prove2.me/submissions/deb56376-3973-4e79-a713-6568838ad271

import Theorems.Thm_MazurTransfer_order27_leaf_tlDCb_s0
import Theorems.Thm_MazurTransfer_order27_leaf_tlDCb_s1

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c0 f ξ + tlDSqP0c1 f ξ + tlDSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f
        ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c3 f ξ + tlDSqP0c4 f ξ + tlDSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP1c0 f ξ + tlDCbP1c1 f ξ) + (tlDCbP1c2 f ξ + tlDCbP1c3 f ξ)) + ((tlDCbP1c4 f
        ξ + tlDCbP1c5 f ξ) + (tlDCbP1c6 f ξ + tlDCbP1c7 f ξ))) + (((tlDCbP1c8 f ξ +
        tlDCbP1c9 f ξ) + (tlDCbP1c10 f ξ + tlDCbP1c11 f ξ)) + tlDCbP1c12 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlDCb_s0, MazurTransfer.order27_leaf_tlDCb_s1⟩

#print axioms solution
