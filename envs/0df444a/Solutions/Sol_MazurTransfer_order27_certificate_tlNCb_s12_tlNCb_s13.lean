-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s12_tlNCb_s13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:18.568367+00:00
-- url     : https://prove2.me/submissions/3f02e1b2-50ea-4c0f-a6e4-dc0e9ceac94d

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s12
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s13

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f ξ + tlNCbP12c3 f ξ)) +
        ((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7 f ξ))) +
        (((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)) +
        ((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ))))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ)) +
        ((tlNCbP13c4 f ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ))) +
        (((tlNCbP13c8 f ξ + tlNCbP13c9 f ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)) +
        ((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) + (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)))) +
        (tlNCbP13c16 f ξ + tlNCbP13c17 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s12, MazurTransfer.order27_leaf_tlNCb_s13⟩

#print axioms solution
