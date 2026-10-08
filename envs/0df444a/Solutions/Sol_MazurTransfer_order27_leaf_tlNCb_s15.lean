-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:33:57.097799+00:00
-- url     : https://prove2.me/submissions/1dc51030-e4f5-4e46-99c5-c2bfefd25c51

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s15 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) +
        ((tlNCbP15c4 f ξ + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ))) +
        (((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) +
        ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ)))) +
        ((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + tlNCbP15c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ15c0 f ξ) * hT + (tlNCbQ15c1 f ξ) * hT + (tlNCbQ15c2 f ξ) * hT + (tlNCbQ15c3 f ξ) * hT
      + (tlNCbQ15c4 f ξ) * hT + (tlNCbQ15c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP15c0, tlNCbP15c1, tlNCbP15c10, tlNCbP15c11,
      tlNCbP15c12, tlNCbP15c13, tlNCbP15c14, tlNCbP15c15, tlNCbP15c16, tlNCbP15c17,
      tlNCbP15c18, tlNCbP15c2, tlNCbP15c3, tlNCbP15c4, tlNCbP15c5, tlNCbP15c6,
      tlNCbP15c7, tlNCbP15c8, tlNCbP15c9, tlNCbQ15c0, tlNCbQ15c1, tlNCbQ15c2,
      tlNCbQ15c3, tlNCbQ15c4, tlNCbQ15c5, tlNSqP1c7, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) +
        ((tlNCbP15c4 f ξ + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ))) +
        (((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) +
        ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ)))) +
        ((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + tlNCbP15c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s15

#print axioms solution
