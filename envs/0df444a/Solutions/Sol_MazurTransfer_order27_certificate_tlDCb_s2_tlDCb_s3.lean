-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlDCb_s2_tlDCb_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:44:40.563646+00:00
-- url     : https://prove2.me/submissions/5e65de2a-b780-4db7-a6db-7f13afb4b7a5

import Theorems.Thm_MazurTransfer_order27_leaf_tlDCb_s2
import Theorems.Thm_MazurTransfer_order27_leaf_tlDCb_s3

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c6 f ξ + tlDSqP0c7 f ξ + tlDSqP0c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP2c0 f ξ + tlDCbP2c1 f ξ) + (tlDCbP2c2 f ξ + tlDCbP2c3 f ξ)) + ((tlDCbP2c4 f
        ξ + tlDCbP2c5 f ξ) + (tlDCbP2c6 f ξ + tlDCbP2c7 f ξ))) + (((tlDCbP2c8 f ξ +
        tlDCbP2c9 f ξ) + (tlDCbP2c10 f ξ + tlDCbP2c11 f ξ)) + (tlDCbP2c12 f ξ + tlDCbP2c13
        f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) + (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ)) + ((tlDCbP3c4 f
        ξ + tlDCbP3c5 f ξ) + (tlDCbP3c6 f ξ + tlDCbP3c7 f ξ))) + ((tlDCbP3c8 f ξ +
        tlDCbP3c9 f ξ) + (tlDCbP3c10 f ξ + tlDCbP3c11 f ξ))) := by
  exact ⟨MazurTransfer.order27_leaf_tlDCb_s2, MazurTransfer.order27_leaf_tlDCb_s3⟩

#print axioms solution
