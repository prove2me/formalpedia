-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s28_tlNCb_s29
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:23.66253+00:00
-- url     : https://prove2.me/submissions/1eadb7c8-bba0-4204-a02f-255b02f5a8de

import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s28
import Theorems.Thm_MazurTransfer_order27_leaf_tlNCb_s29

open MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c10 f ξ + tlNSqP2c11 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP28c0 f ξ + tlNCbP28c1 f ξ) + (tlNCbP28c2 f ξ + tlNCbP28c3 f ξ)) +
        ((tlNCbP28c4 f ξ + tlNCbP28c5 f ξ) + (tlNCbP28c6 f ξ + tlNCbP28c7 f ξ))) +
        (((tlNCbP28c8 f ξ + tlNCbP28c9 f ξ) + (tlNCbP28c10 f ξ + tlNCbP28c11 f ξ)) +
        ((tlNCbP28c12 f ξ + tlNCbP28c13 f ξ) + (tlNCbP28c14 f ξ + tlNCbP28c15 f ξ)))) +
        ((tlNCbP28c16 f ξ + tlNCbP28c17 f ξ) + tlNCbP28c18 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP29c0 f ξ + tlNCbP29c1 f ξ) + (tlNCbP29c2 f ξ + tlNCbP29c3 f ξ)) +
        ((tlNCbP29c4 f ξ + tlNCbP29c5 f ξ) + (tlNCbP29c6 f ξ + tlNCbP29c7 f ξ))) +
        ((tlNCbP29c8 f ξ + tlNCbP29c9 f ξ) + tlNCbP29c10 f ξ)) := by
  exact ⟨MazurTransfer.order27_leaf_tlNCb_s28, MazurTransfer.order27_leaf_tlNCb_s29⟩

#print axioms solution
