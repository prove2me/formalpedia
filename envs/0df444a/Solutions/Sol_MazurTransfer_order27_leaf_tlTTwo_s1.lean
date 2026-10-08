-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:40:12.280926+00:00
-- url     : https://prove2.me/submissions/8601ec63-a6c1-459c-9679-578e783b4f48

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ1c0 f ξ) * hT + (tlTTwoQ1c1 f ξ) * hT + (tlTTwoQ1c2 f ξ) * hT + (tlTTwoQ1c3 f ξ) * hT
      + (tlTTwoQ1c4 f ξ) * hT + (tlTTwoQ1c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP0c3, tlNSqP0c4, tlNSqP0c5, tlT0, tlT1, tlT2, tlT3, tlTTwoP1c0,
      tlTTwoP1c1, tlTTwoP1c10, tlTTwoP1c11, tlTTwoP1c12, tlTTwoP1c2, tlTTwoP1c3,
      tlTTwoP1c4, tlTTwoP1c5, tlTTwoP1c6, tlTTwoP1c7, tlTTwoP1c8, tlTTwoP1c9,
      tlTTwoQ1c0, tlTTwoQ1c1, tlTTwoQ1c2, tlTTwoQ1c3, tlTTwoQ1c4, tlTTwoQ1c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTTwo_s1

#print axioms solution
