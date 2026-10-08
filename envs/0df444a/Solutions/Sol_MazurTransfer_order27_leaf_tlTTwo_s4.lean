-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:42:59.798282+00:00
-- url     : https://prove2.me/submissions/2f9e7a83-e3cc-41ce-8d86-76f2147eb39f

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ) + (tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ)) +
        ((tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ) + (tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ))) +
        (((tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ) + (tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ)) +
        (tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ4c0 f ξ) * hT + (tlTTwoQ4c1 f ξ) * hT + (tlTTwoQ4c2 f ξ) * hT + (tlTTwoQ4c3 f ξ) * hT
      + (tlTTwoQ4c4 f ξ) * hT + (tlTTwoQ4c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP1c4, tlNSqP1c5, tlNSqP1c6, tlT0, tlT1, tlT2, tlT3, tlTTwoP4c0,
      tlTTwoP4c1, tlTTwoP4c10, tlTTwoP4c11, tlTTwoP4c12, tlTTwoP4c13, tlTTwoP4c2,
      tlTTwoP4c3, tlTTwoP4c4, tlTTwoP4c5, tlTTwoP4c6, tlTTwoP4c7, tlTTwoP4c8,
      tlTTwoP4c9, tlTTwoQ4c0, tlTTwoQ4c1, tlTTwoQ4c2, tlTTwoQ4c3, tlTTwoQ4c4,
      tlTTwoQ4c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ) + (tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ)) +
        ((tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ) + (tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ))) +
        (((tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ) + (tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ)) +
        (tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ))) := by
  exact MazurTorsion.Kubert.tlTTwo_s4

#print axioms solution
