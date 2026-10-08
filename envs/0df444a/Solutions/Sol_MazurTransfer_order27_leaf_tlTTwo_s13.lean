-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:47:17.708173+00:00
-- url     : https://prove2.me/submissions/b63c359f-65a4-435d-a5fc-906640b7346b

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s13 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ) + (tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ)) +
        ((tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ) + (tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ))) +
        (((tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ) + (tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ)) +
        tlTTwoP13c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ13c0 f ξ) * hT + (tlTTwoQ13c1 f ξ) * hT + (tlTTwoQ13c2 f ξ) * hT + (tlTTwoQ13c3 f ξ) *
      hT + (tlTTwoQ13c4 f ξ) * hT + (tlTTwoQ13c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c10, tlNSqP3c11, tlT0, tlT1, tlT2, tlT3, tlTTwoP13c0,
      tlTTwoP13c1, tlTTwoP13c10, tlTTwoP13c11, tlTTwoP13c12, tlTTwoP13c2,
      tlTTwoP13c3, tlTTwoP13c4, tlTTwoP13c5, tlTTwoP13c6, tlTTwoP13c7, tlTTwoP13c8,
      tlTTwoP13c9, tlTTwoQ13c0, tlTTwoQ13c1, tlTTwoQ13c2, tlTTwoQ13c3, tlTTwoQ13c4,
      tlTTwoQ13c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c10 f ξ + tlNSqP3c11 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ) + (tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ)) +
        ((tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ) + (tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ))) +
        (((tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ) + (tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ)) +
        tlTTwoP13c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTTwo_s13

#print axioms solution
