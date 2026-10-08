-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s25
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:44.737976+00:00
-- url     : https://prove2.me/submissions/14cc5228-a078-45c9-9993-b58713575c00

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s25 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP25c0 f + tlNCbP25c1 f ξ) + (tlNCbP25c2 f ξ + tlNCbP25c3 f ξ)) +
        ((tlNCbP25c4 f ξ + tlNCbP25c5 f ξ) + (tlNCbP25c6 f ξ + tlNCbP25c7 f ξ))) +
        (((tlNCbP25c8 f ξ + tlNCbP25c9 f ξ) + (tlNCbP25c10 f ξ + tlNCbP25c11 f ξ)) +
        ((tlNCbP25c12 f ξ + tlNCbP25c13 f ξ) + (tlNCbP25c14 f ξ + tlNCbP25c15 f ξ)))) +
        ((tlNCbP25c16 f ξ + tlNCbP25c17 f ξ) + tlNCbP25c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ25c0 f ξ) * hT + (tlNCbQ25c1 f ξ) * hT + (tlNCbQ25c2 f ξ) * hT + (tlNCbQ25c3 f ξ) * hT
      + (tlNCbQ25c4 f ξ) * hT + (tlNCbQ25c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP25c0, tlNCbP25c1, tlNCbP25c10, tlNCbP25c11,
      tlNCbP25c12, tlNCbP25c13, tlNCbP25c14, tlNCbP25c15, tlNCbP25c16, tlNCbP25c17,
      tlNCbP25c18, tlNCbP25c2, tlNCbP25c3, tlNCbP25c4, tlNCbP25c5, tlNCbP25c6,
      tlNCbP25c7, tlNCbP25c8, tlNCbP25c9, tlNCbQ25c0, tlNCbQ25c1, tlNCbQ25c2,
      tlNCbQ25c3, tlNCbQ25c4, tlNCbQ25c5, tlNSqP2c7, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP25c0 f + tlNCbP25c1 f ξ) + (tlNCbP25c2 f ξ + tlNCbP25c3 f ξ)) +
        ((tlNCbP25c4 f ξ + tlNCbP25c5 f ξ) + (tlNCbP25c6 f ξ + tlNCbP25c7 f ξ))) +
        (((tlNCbP25c8 f ξ + tlNCbP25c9 f ξ) + (tlNCbP25c10 f ξ + tlNCbP25c11 f ξ)) +
        ((tlNCbP25c12 f ξ + tlNCbP25c13 f ξ) + (tlNCbP25c14 f ξ + tlNCbP25c15 f ξ)))) +
        ((tlNCbP25c16 f ξ + tlNCbP25c17 f ξ) + tlNCbP25c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s25

#print axioms solution
