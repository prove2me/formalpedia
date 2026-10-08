-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTOne_s4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:25:06.553361+00:00
-- url     : https://prove2.me/submissions/4d31c3a9-1882-48a7-8890-4300f1a12134

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTOne_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)) +
        ((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ))) +
        (((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ)) +
        tlTOneP4c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ4c0 f ξ) * hT + (tlTOneQ4c1 f ξ) * hT + (tlTOneQ4c2 f ξ) * hT + (tlTOneQ4c3 f ξ) * hT
      + (tlTOneQ4c4 f ξ) * hT + (tlTOneQ4c5 f ξ) * hT
  simp only [tlDSqP0c4, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP4c0,
      tlTOneP4c1, tlTOneP4c10, tlTOneP4c11, tlTOneP4c12, tlTOneP4c2, tlTOneP4c3,
      tlTOneP4c4, tlTOneP4c5, tlTOneP4c6, tlTOneP4c7, tlTOneP4c8, tlTOneP4c9,
      tlTOneQ4c0, tlTOneQ4c1, tlTOneQ4c2, tlTOneQ4c3, tlTOneQ4c4, tlTOneQ4c5]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlTOne_s4 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)) +
        ((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ))) +
        (((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ)) +
        tlTOneP4c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTOne_s4

#print axioms MazurTransfer.order27_certificate_tlTOne_s4


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)) +
        ((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ))) +
        (((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ)) +
        tlTOneP4c12 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlTOne_s4

#print axioms solution
