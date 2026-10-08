-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:32.024167+00:00
-- url     : https://prove2.me/submissions/a7cf4ca9-bc31-4f7f-8e72-9e47e9d768d7

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ0c0 f ξ) * hT + (tlTTwoQ0c1 f ξ) * hT + (tlTTwoQ0c2 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP0c0, tlNSqP0c1, tlNSqP0c2, tlT0, tlT1, tlT2, tlT3, tlTTwoP0c0,
      tlTTwoP0c1, tlTTwoP0c2, tlTTwoP0c3, tlTTwoP0c4, tlTTwoP0c5, tlTTwoP0c6,
      tlTTwoP0c7, tlTTwoP0c8, tlTTwoP0c9, tlTTwoQ0c0, tlTTwoQ0c1, tlTTwoQ0c2]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ)) := by
  exact MazurTorsion.Kubert.tlTTwo_s0

#print axioms solution
