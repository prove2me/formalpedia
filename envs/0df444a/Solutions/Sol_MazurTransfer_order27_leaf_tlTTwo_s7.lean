-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:44:26.349703+00:00
-- url     : https://prove2.me/submissions/ba3a9132-6e15-4ab7-9993-9a584aad0770

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ) + (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ)) +
        ((tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ) + (tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ))) +
        (((tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ) + (tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ)) +
        tlTTwoP7c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ7c0 f ξ) * hT + (tlTTwoQ7c1 f ξ) * hT + (tlTTwoQ7c2 f ξ) * hT + (tlTTwoQ7c3 f ξ) * hT
      + (tlTTwoQ7c4 f ξ) * hT + (tlTTwoQ7c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c3, tlNSqP2c4, tlNSqP2c5, tlT0, tlT1, tlT2, tlT3, tlTTwoP7c0,
      tlTTwoP7c1, tlTTwoP7c10, tlTTwoP7c11, tlTTwoP7c12, tlTTwoP7c2, tlTTwoP7c3,
      tlTTwoP7c4, tlTTwoP7c5, tlTTwoP7c6, tlTTwoP7c7, tlTTwoP7c8, tlTTwoP7c9,
      tlTTwoQ7c0, tlTTwoQ7c1, tlTTwoQ7c2, tlTTwoQ7c3, tlTTwoQ7c4, tlTTwoQ7c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ) + (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ)) +
        ((tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ) + (tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ))) +
        (((tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ) + (tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ)) +
        tlTTwoP7c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTTwo_s7

#print axioms solution
