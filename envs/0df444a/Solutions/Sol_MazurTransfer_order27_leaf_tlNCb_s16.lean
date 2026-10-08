-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s16
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:53.113274+00:00
-- url     : https://prove2.me/submissions/e743f351-d8c9-455f-907c-052cefc50a60

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s16 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP16c0 f ξ + tlNCbP16c1 f ξ) + (tlNCbP16c2 f ξ + tlNCbP16c3 f ξ)) +
        ((tlNCbP16c4 f ξ + tlNCbP16c5 f ξ) + (tlNCbP16c6 f ξ + tlNCbP16c7 f ξ))) +
        (((tlNCbP16c8 f ξ + tlNCbP16c9 f ξ) + (tlNCbP16c10 f ξ + tlNCbP16c11 f ξ)) +
        ((tlNCbP16c12 f ξ + tlNCbP16c13 f ξ) + (tlNCbP16c14 f ξ + tlNCbP16c15 f ξ)))) +
        ((tlNCbP16c16 f ξ + tlNCbP16c17 f ξ) + tlNCbP16c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ16c0 f ξ) * hT + (tlNCbQ16c1 f ξ) * hT + (tlNCbQ16c2 f ξ) * hT + (tlNCbQ16c3 f ξ) * hT
      + (tlNCbQ16c4 f ξ) * hT + (tlNCbQ16c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP16c0, tlNCbP16c1, tlNCbP16c10, tlNCbP16c11,
      tlNCbP16c12, tlNCbP16c13, tlNCbP16c14, tlNCbP16c15, tlNCbP16c16, tlNCbP16c17,
      tlNCbP16c18, tlNCbP16c2, tlNCbP16c3, tlNCbP16c4, tlNCbP16c5, tlNCbP16c6,
      tlNCbP16c7, tlNCbP16c8, tlNCbP16c9, tlNCbQ16c0, tlNCbQ16c1, tlNCbQ16c2,
      tlNCbQ16c3, tlNCbQ16c4, tlNCbQ16c5, tlNSqP1c8, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP16c0 f ξ + tlNCbP16c1 f ξ) + (tlNCbP16c2 f ξ + tlNCbP16c3 f ξ)) +
        ((tlNCbP16c4 f ξ + tlNCbP16c5 f ξ) + (tlNCbP16c6 f ξ + tlNCbP16c7 f ξ))) +
        (((tlNCbP16c8 f ξ + tlNCbP16c9 f ξ) + (tlNCbP16c10 f ξ + tlNCbP16c11 f ξ)) +
        ((tlNCbP16c12 f ξ + tlNCbP16c13 f ξ) + (tlNCbP16c14 f ξ + tlNCbP16c15 f ξ)))) +
        ((tlNCbP16c16 f ξ + tlNCbP16c17 f ξ) + tlNCbP16c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s16

#print axioms solution
