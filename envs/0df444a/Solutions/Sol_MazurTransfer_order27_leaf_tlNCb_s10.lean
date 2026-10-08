-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:32:37.173531+00:00
-- url     : https://prove2.me/submissions/678f4f47-d4bc-4d69-810c-78b9294b0e95

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s10 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP10c0 f ξ + tlNCbP10c1 f ξ) + (tlNCbP10c2 f ξ + tlNCbP10c3 f ξ)) +
        ((tlNCbP10c4 f ξ + tlNCbP10c5 f ξ) + (tlNCbP10c6 f ξ + tlNCbP10c7 f ξ))) +
        (((tlNCbP10c8 f ξ + tlNCbP10c9 f ξ) + (tlNCbP10c10 f ξ + tlNCbP10c11 f ξ)) +
        (tlNCbP10c12 f ξ + tlNCbP10c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ10c0 f ξ) * hT + (tlNCbQ10c1 f ξ) * hT + (tlNCbQ10c2 f ξ) * hT + (tlNCbQ10c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP10c0, tlNCbP10c1, tlNCbP10c10, tlNCbP10c11,
      tlNCbP10c12, tlNCbP10c13, tlNCbP10c2, tlNCbP10c3, tlNCbP10c4, tlNCbP10c5,
      tlNCbP10c6, tlNCbP10c7, tlNCbP10c8, tlNCbP10c9, tlNCbQ10c0, tlNCbQ10c1,
      tlNCbQ10c2, tlNCbQ10c3, tlNSqP1c2, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP10c0 f ξ + tlNCbP10c1 f ξ) + (tlNCbP10c2 f ξ + tlNCbP10c3 f ξ)) +
        ((tlNCbP10c4 f ξ + tlNCbP10c5 f ξ) + (tlNCbP10c6 f ξ + tlNCbP10c7 f ξ))) +
        (((tlNCbP10c8 f ξ + tlNCbP10c9 f ξ) + (tlNCbP10c10 f ξ + tlNCbP10c11 f ξ)) +
        (tlNCbP10c12 f ξ + tlNCbP10c13 f ξ))) := by
  exact MazurTorsion.Kubert.tlNCb_s10

#print axioms solution
