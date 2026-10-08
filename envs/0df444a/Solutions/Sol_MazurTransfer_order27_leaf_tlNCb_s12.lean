-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:32:39.205028+00:00
-- url     : https://prove2.me/submissions/dad512c7-5965-41c3-b686-11f5643fa297

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s12 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f ξ + tlNCbP12c3 f ξ)) +
        ((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7 f ξ))) +
        (((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)) +
        ((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ12c0 f ξ) * hT + (tlNCbQ12c1 f ξ) * hT + (tlNCbQ12c2 f ξ) * hT + (tlNCbQ12c3 f ξ) * hT
      + (tlNCbQ12c4 f ξ) * hT + (tlNCbQ12c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP12c0, tlNCbP12c1, tlNCbP12c10, tlNCbP12c11,
      tlNCbP12c12, tlNCbP12c13, tlNCbP12c14, tlNCbP12c15, tlNCbP12c2, tlNCbP12c3,
      tlNCbP12c4, tlNCbP12c5, tlNCbP12c6, tlNCbP12c7, tlNCbP12c8, tlNCbP12c9,
      tlNCbQ12c0, tlNCbQ12c1, tlNCbQ12c2, tlNCbQ12c3, tlNCbQ12c4, tlNCbQ12c5,
      tlNSqP1c4, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f ξ + tlNCbP12c3 f ξ)) +
        ((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7 f ξ))) +
        (((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)) +
        ((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ)))) := by
  exact MazurTorsion.Kubert.tlNCb_s12

#print axioms solution
