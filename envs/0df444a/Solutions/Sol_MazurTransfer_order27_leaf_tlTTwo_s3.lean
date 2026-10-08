-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:42:58.591671+00:00
-- url     : https://prove2.me/submissions/12729b3f-bfb1-4a7a-96a4-bcb2aed45a05

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ + tlNSqP1c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ) + (tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ)) +
        ((tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) + (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ))) +
        ((tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ) + (tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ3c0 f ξ) * hT + (tlTTwoQ3c1 f ξ) * hT + (tlTTwoQ3c2 f ξ) * hT + (tlTTwoQ3c3 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP1c1, tlNSqP1c2, tlNSqP1c3, tlT0, tlT1, tlT2, tlT3, tlTTwoP3c0,
      tlTTwoP3c1, tlTTwoP3c10, tlTTwoP3c11, tlTTwoP3c2, tlTTwoP3c3, tlTTwoP3c4,
      tlTTwoP3c5, tlTTwoP3c6, tlTTwoP3c7, tlTTwoP3c8, tlTTwoP3c9, tlTTwoQ3c0,
      tlTTwoQ3c1, tlTTwoQ3c2, tlTTwoQ3c3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c1 f ξ + tlNSqP1c2 f ξ + tlNSqP1c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ) + (tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ)) +
        ((tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) + (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ))) +
        ((tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ) + (tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ))) := by
  exact MazurTorsion.Kubert.tlTTwo_s3

#print axioms solution
