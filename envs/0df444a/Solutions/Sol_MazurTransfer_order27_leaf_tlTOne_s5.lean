-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTOne_s5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:40:57.561755+00:00
-- url     : https://prove2.me/submissions/e8a653ff-8360-46e7-99b2-8f74ad649d0e

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

lemma tlTOne_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP5c0 f ξ + tlTOneP5c1 f ξ) + (tlTOneP5c2 f ξ + tlTOneP5c3 f ξ)) +
        ((tlTOneP5c4 f ξ + tlTOneP5c5 f ξ) + (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ))) +
        (((tlTOneP5c8 f ξ + tlTOneP5c9 f ξ) + (tlTOneP5c10 f ξ + tlTOneP5c11 f ξ)) +
        tlTOneP5c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ5c0 f ξ) * hT + (tlTOneQ5c1 f ξ) * hT + (tlTOneQ5c2 f ξ) * hT + (tlTOneQ5c3 f ξ) * hT
      + (tlTOneQ5c4 f ξ) * hT + (tlTOneQ5c5 f ξ) * hT
  simp only [tlDSqP0c5, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP5c0,
      tlTOneP5c1, tlTOneP5c10, tlTOneP5c11, tlTOneP5c12, tlTOneP5c2, tlTOneP5c3,
      tlTOneP5c4, tlTOneP5c5, tlTOneP5c6, tlTOneP5c7, tlTOneP5c8, tlTOneP5c9,
      tlTOneQ5c0, tlTOneQ5c1, tlTOneQ5c2, tlTOneQ5c3, tlTOneQ5c4, tlTOneQ5c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP5c0 f ξ + tlTOneP5c1 f ξ) + (tlTOneP5c2 f ξ + tlTOneP5c3 f ξ)) +
        ((tlTOneP5c4 f ξ + tlTOneP5c5 f ξ) + (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ))) +
        (((tlTOneP5c8 f ξ + tlTOneP5c9 f ξ) + (tlTOneP5c10 f ξ + tlTOneP5c11 f ξ)) +
        tlTOneP5c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTOne_s5

#print axioms solution
