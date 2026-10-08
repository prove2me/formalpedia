-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTOne_s5_tlTOne_s6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:42:14.02533+00:00
-- url     : https://prove2.me/submissions/20a8a0fe-d13e-467c-b087-af3ac257564b

import Theorems.Thm_MazurTransfer_order27_leaf_tlTOne_s5
import Theorems.Thm_MazurTransfer_order27_leaf_tlTOne_s6

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP5c0 f ξ + tlTOneP5c1 f ξ) + (tlTOneP5c2 f ξ + tlTOneP5c3 f ξ)) +
        ((tlTOneP5c4 f ξ + tlTOneP5c5 f ξ) + (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ))) +
        (((tlTOneP5c8 f ξ + tlTOneP5c9 f ξ) + (tlTOneP5c10 f ξ + tlTOneP5c11 f ξ)) +
        tlTOneP5c12 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP6c0 f ξ + tlTOneP6c1 f ξ) + (tlTOneP6c2 f ξ + tlTOneP6c3 f ξ)) +
        ((tlTOneP6c4 f ξ + tlTOneP6c5 f ξ) + (tlTOneP6c6 f ξ + tlTOneP6c7 f ξ))) +
        (((tlTOneP6c8 f ξ + tlTOneP6c9 f ξ) + (tlTOneP6c10 f ξ + tlTOneP6c11 f ξ)) +
        tlTOneP6c12 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlTOne_s5, MazurTransfer.order27_leaf_tlTOne_s6⟩

#print axioms solution
