-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTOne_s8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:41:35.291021+00:00
-- url     : https://prove2.me/submissions/37fff594-181d-4f26-b615-ae87367b5012

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

lemma tlTOne_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        tlTOneP8c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ8c0 f ξ) * hT + (tlTOneQ8c1 f ξ) * hT + (tlTOneQ8c2 f ξ) * hT + (tlTOneQ8c3 f ξ) * hT
      + (tlTOneQ8c4 f ξ) * hT + (tlTOneQ8c5 f ξ) * hT
  simp only [tlDSqP0c8, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP8c0,
      tlTOneP8c1, tlTOneP8c10, tlTOneP8c11, tlTOneP8c12, tlTOneP8c2, tlTOneP8c3,
      tlTOneP8c4, tlTOneP8c5, tlTOneP8c6, tlTOneP8c7, tlTOneP8c8, tlTOneP8c9,
      tlTOneQ8c0, tlTOneQ8c1, tlTOneQ8c2, tlTOneQ8c3, tlTOneQ8c4, tlTOneQ8c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        tlTOneP8c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTOne_s8

#print axioms solution
