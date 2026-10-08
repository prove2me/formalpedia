-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:45:52.623561+00:00
-- url     : https://prove2.me/submissions/2a95df01-f820-4b1c-8a5c-70763096c1cb

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s11 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c4 f ξ + tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ) + (tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ)) +
        ((tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ) + (tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ))) +
        (((tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ) + (tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ)) +
        (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ11c0 f ξ) * hT + (tlTTwoQ11c1 f ξ) * hT + (tlTTwoQ11c2 f ξ) * hT + (tlTTwoQ11c3 f ξ) *
      hT + (tlTTwoQ11c4 f ξ) * hT + (tlTTwoQ11c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c4, tlNSqP3c5, tlNSqP3c6, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP11c0, tlTTwoP11c1, tlTTwoP11c10, tlTTwoP11c11, tlTTwoP11c12,
      tlTTwoP11c13, tlTTwoP11c2, tlTTwoP11c3, tlTTwoP11c4, tlTTwoP11c5, tlTTwoP11c6,
      tlTTwoP11c7, tlTTwoP11c8, tlTTwoP11c9, tlTTwoQ11c0, tlTTwoQ11c1, tlTTwoQ11c2,
      tlTTwoQ11c3, tlTTwoQ11c4, tlTTwoQ11c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c4 f ξ + tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ) + (tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ)) +
        ((tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ) + (tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ))) +
        (((tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ) + (tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ)) +
        (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ))) := by
  exact MazurTorsion.Kubert.tlTTwo_s11

#print axioms solution
