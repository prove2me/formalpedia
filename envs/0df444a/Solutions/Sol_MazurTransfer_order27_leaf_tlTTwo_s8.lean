-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:45:49.36272+00:00
-- url     : https://prove2.me/submissions/5eb77117-c77e-4f20-993f-d2e38bcecdc5

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ) + (tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ)) +
        ((tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ) + (tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ))) +
        (((tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ) + (tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ)) +
        (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ8c0 f ξ) * hT + (tlTTwoQ8c1 f ξ) * hT + (tlTTwoQ8c2 f ξ) * hT + (tlTTwoQ8c3 f ξ) * hT
      + (tlTTwoQ8c4 f ξ) * hT + (tlTTwoQ8c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c6, tlNSqP2c7, tlNSqP2c8, tlT0, tlT1, tlT2, tlT3, tlTTwoP8c0,
      tlTTwoP8c1, tlTTwoP8c10, tlTTwoP8c11, tlTTwoP8c12, tlTTwoP8c13, tlTTwoP8c2,
      tlTTwoP8c3, tlTTwoP8c4, tlTTwoP8c5, tlTTwoP8c6, tlTTwoP8c7, tlTTwoP8c8,
      tlTTwoP8c9, tlTTwoQ8c0, tlTTwoQ8c1, tlTTwoQ8c2, tlTTwoQ8c3, tlTTwoQ8c4,
      tlTTwoQ8c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ) + (tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ)) +
        ((tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ) + (tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ))) +
        (((tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ) + (tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ)) +
        (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ))) := by
  exact MazurTorsion.Kubert.tlTTwo_s8

#print axioms solution
