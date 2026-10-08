-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTOne_s7_tlTOne_s8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:41:36.302184+00:00
-- url     : https://prove2.me/submissions/16f01af7-5efd-450a-a86a-1b93fa65d0cf

import Theorems.Thm_MazurTransfer_order27_leaf_tlTOne_s7
import Theorems.Thm_MazurTransfer_order27_leaf_tlTOne_s8

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP7c0 f ξ + tlTOneP7c1 f ξ) + (tlTOneP7c2 f ξ + tlTOneP7c3 f ξ)) +
        ((tlTOneP7c4 f ξ + tlTOneP7c5 f ξ) + (tlTOneP7c6 f ξ + tlTOneP7c7 f ξ))) +
        (((tlTOneP7c8 f ξ + tlTOneP7c9 f ξ) + (tlTOneP7c10 f ξ + tlTOneP7c11 f ξ)) +
        tlTOneP7c12 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        tlTOneP8c12 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlTOne_s7, MazurTransfer.order27_leaf_tlTOne_s8⟩

#print axioms solution
