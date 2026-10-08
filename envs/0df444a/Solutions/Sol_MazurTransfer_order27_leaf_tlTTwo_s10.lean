-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:45:51.312049+00:00
-- url     : https://prove2.me/submissions/69c53c8e-3ac0-4126-ae7f-140b6e32184f

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s10 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) + (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ)) +
        ((tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ) + (tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ))) +
        ((tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ) + (tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ10c0 f ξ) * hT + (tlTTwoQ10c1 f ξ) * hT + (tlTTwoQ10c2 f ξ) * hT + (tlTTwoQ10c3 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP3c1, tlNSqP3c2, tlNSqP3c3, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP10c0, tlTTwoP10c1, tlTTwoP10c10, tlTTwoP10c11, tlTTwoP10c2,
      tlTTwoP10c3, tlTTwoP10c4, tlTTwoP10c5, tlTTwoP10c6, tlTTwoP10c7, tlTTwoP10c8,
      tlTTwoP10c9, tlTTwoQ10c0, tlTTwoQ10c1, tlTTwoQ10c2, tlTTwoQ10c3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) + (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ)) +
        ((tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ) + (tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ))) +
        ((tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ) + (tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ))) := by
  exact MazurTorsion.Kubert.tlTTwo_s10

#print axioms solution
