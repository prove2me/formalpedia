-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:47:16.610861+00:00
-- url     : https://prove2.me/submissions/ba00d0cc-a13a-41d8-af0b-f841a5586230

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s12 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ + tlNSqP3c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) + (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) +
        ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ))) +
        (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ)) +
        (tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ12c0 f ξ) * hT + (tlTTwoQ12c1 f ξ) * hT + (tlTTwoQ12c2 f ξ) * hT + (tlTTwoQ12c3 f ξ) *
      hT + (tlTTwoQ12c4 f ξ) * hT + (tlTTwoQ12c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c7, tlNSqP3c8, tlNSqP3c9, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP12c0, tlTTwoP12c1, tlTTwoP12c10, tlTTwoP12c11, tlTTwoP12c12,
      tlTTwoP12c13, tlTTwoP12c2, tlTTwoP12c3, tlTTwoP12c4, tlTTwoP12c5, tlTTwoP12c6,
      tlTTwoP12c7, tlTTwoP12c8, tlTTwoP12c9, tlTTwoQ12c0, tlTTwoQ12c1, tlTTwoQ12c2,
      tlTTwoQ12c3, tlTTwoQ12c4, tlTTwoQ12c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c7 f ξ + tlNSqP3c8 f ξ + tlNSqP3c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) + (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) +
        ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ))) +
        (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ)) +
        (tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ))) := by
  exact MazurTorsion.Kubert.tlTTwo_s12

#print axioms solution
