-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s4_tlNCb_s5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:29:04.541766+00:00
-- url     : https://prove2.me/submissions/e5affa0d-f52b-4c4b-81a6-129249562d99

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s4
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s5

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP4c0 f ξ + tlNCbP4c1 f ξ) + (tlNCbP4c2 f ξ + tlNCbP4c3 f ξ)) + ((tlNCbP4c4
        f ξ + tlNCbP4c5 f ξ) + (tlNCbP4c6 f ξ + tlNCbP4c7 f ξ))) + (((tlNCbP4c8 f ξ +
        tlNCbP4c9 f ξ) + (tlNCbP4c10 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP4c12 f ξ +
        tlNCbP4c13 f ξ) + (tlNCbP4c14 f ξ + tlNCbP4c15 f ξ)))) + tlNCbP4c16 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4
        f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ))) + (((tlNCbP5c8 f ξ +
        tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ +
        tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ)))) + (tlNCbP5c16 f ξ +
        tlNCbP5c17 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s4, MazurTransfer.order27_leaf_tlNCb_s5⟩

#print axioms solution
