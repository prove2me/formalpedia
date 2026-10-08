-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTOne_s7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:40:59.017783+00:00
-- url     : https://prove2.me/submissions/18968b34-3b3f-4878-be2a-9d57d0bb8a12

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTOne_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP7c0 f ξ + tlTOneP7c1 f ξ) + (tlTOneP7c2 f ξ + tlTOneP7c3 f ξ)) +
        ((tlTOneP7c4 f ξ + tlTOneP7c5 f ξ) + (tlTOneP7c6 f ξ + tlTOneP7c7 f ξ))) +
        (((tlTOneP7c8 f ξ + tlTOneP7c9 f ξ) + (tlTOneP7c10 f ξ + tlTOneP7c11 f ξ)) +
        tlTOneP7c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ7c0 f ξ) * hT + (tlTOneQ7c1 f ξ) * hT + (tlTOneQ7c2 f ξ) * hT + (tlTOneQ7c3 f ξ) * hT
      + (tlTOneQ7c4 f ξ) * hT + (tlTOneQ7c5 f ξ) * hT
  simp only [tlDSqP0c7, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP7c0,
      tlTOneP7c1, tlTOneP7c10, tlTOneP7c11, tlTOneP7c12, tlTOneP7c2, tlTOneP7c3,
      tlTOneP7c4, tlTOneP7c5, tlTOneP7c6, tlTOneP7c7, tlTOneP7c8, tlTOneP7c9,
      tlTOneQ7c0, tlTOneQ7c1, tlTOneQ7c2, tlTOneQ7c3, tlTOneQ7c4, tlTOneQ7c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP7c0 f ξ + tlTOneP7c1 f ξ) + (tlTOneP7c2 f ξ + tlTOneP7c3 f ξ)) +
        ((tlTOneP7c4 f ξ + tlTOneP7c5 f ξ) + (tlTOneP7c6 f ξ + tlTOneP7c7 f ξ))) +
        (((tlTOneP7c8 f ξ + tlTOneP7c9 f ξ) + (tlTOneP7c10 f ξ + tlTOneP7c11 f ξ)) +
        tlTOneP7c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTOne_s7

#print axioms solution
