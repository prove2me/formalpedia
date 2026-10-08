-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTOne_s6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:42:13.111351+00:00
-- url     : https://prove2.me/submissions/34e6ae07-5bd0-4ba0-8bf9-994d866d722b

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

lemma tlTOne_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP6c0 f ξ + tlTOneP6c1 f ξ) + (tlTOneP6c2 f ξ + tlTOneP6c3 f ξ)) +
        ((tlTOneP6c4 f ξ + tlTOneP6c5 f ξ) + (tlTOneP6c6 f ξ + tlTOneP6c7 f ξ))) +
        (((tlTOneP6c8 f ξ + tlTOneP6c9 f ξ) + (tlTOneP6c10 f ξ + tlTOneP6c11 f ξ)) +
        tlTOneP6c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ6c0 f ξ) * hT + (tlTOneQ6c1 f ξ) * hT + (tlTOneQ6c2 f ξ) * hT + (tlTOneQ6c3 f ξ) * hT
      + (tlTOneQ6c4 f ξ) * hT + (tlTOneQ6c5 f ξ) * hT
  simp only [tlDSqP0c6, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP6c0,
      tlTOneP6c1, tlTOneP6c10, tlTOneP6c11, tlTOneP6c12, tlTOneP6c2, tlTOneP6c3,
      tlTOneP6c4, tlTOneP6c5, tlTOneP6c6, tlTOneP6c7, tlTOneP6c8, tlTOneP6c9,
      tlTOneQ6c0, tlTOneQ6c1, tlTOneQ6c2, tlTOneQ6c3, tlTOneQ6c4, tlTOneQ6c5]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP6c0 f ξ + tlTOneP6c1 f ξ) + (tlTOneP6c2 f ξ + tlTOneP6c3 f ξ)) +
        ((tlTOneP6c4 f ξ + tlTOneP6c5 f ξ) + (tlTOneP6c6 f ξ + tlTOneP6c7 f ξ))) +
        (((tlTOneP6c8 f ξ + tlTOneP6c9 f ξ) + (tlTOneP6c10 f ξ + tlTOneP6c11 f ξ)) +
        tlTOneP6c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTOne_s6

#print axioms solution
