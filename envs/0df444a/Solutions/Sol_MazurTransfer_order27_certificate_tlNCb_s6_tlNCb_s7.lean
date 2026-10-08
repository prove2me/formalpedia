-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s6_tlNCb_s7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:36:42.602127+00:00
-- url     : https://prove2.me/submissions/230e9703-17ce-418f-bf4c-49b4a1a3529c

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s6
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s7

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP6c0 f ξ + tlNCbP6c1 f ξ) + (tlNCbP6c2 f ξ + tlNCbP6c3 f ξ)) + ((tlNCbP6c4
        f ξ + tlNCbP6c5 f ξ) + (tlNCbP6c6 f ξ + tlNCbP6c7 f ξ))) + (((tlNCbP6c8 f ξ +
        tlNCbP6c9 f ξ) + (tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)) + ((tlNCbP6c12 f ξ +
        tlNCbP6c13 f ξ) + (tlNCbP6c14 f ξ + tlNCbP6c15 f ξ)))) + (tlNCbP6c16 f ξ +
        tlNCbP6c17 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c7 f ξ + tlNSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)) + ((tlNCbP7c4
        f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP7c8 f ξ +
        tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ)) + ((tlNCbP7c12 f ξ +
        tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)))) + ((tlNCbP7c16 f ξ +
        tlNCbP7c17 f ξ) + tlNCbP7c18 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s6, MazurTransfer.order27_leaf_tlNCb_s7⟩

#print axioms solution
