-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTOne_s9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:25:10.612193+00:00
-- url     : https://prove2.me/submissions/efb47a78-4c20-4390-8e80-0292dd1c95cc

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

lemma tlTOne_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP9c0 f ξ + tlTOneP9c1 f ξ) + (tlTOneP9c2 f ξ + tlTOneP9c3 f ξ)) +
        ((tlTOneP9c4 f ξ + tlTOneP9c5 f ξ) + (tlTOneP9c6 f ξ + tlTOneP9c7 f ξ))) +
        (((tlTOneP9c8 f ξ + tlTOneP9c9 f ξ) + (tlTOneP9c10 f ξ + tlTOneP9c11 f ξ)) +
        tlTOneP9c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ9c0 f ξ) * hT + (tlTOneQ9c1 f ξ) * hT + (tlTOneQ9c2 f ξ) * hT + (tlTOneQ9c3 f ξ) * hT
      + (tlTOneQ9c4 f ξ) * hT + (tlTOneQ9c5 f ξ) * hT
  simp only [tlDSqP0c9, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP9c0,
      tlTOneP9c1, tlTOneP9c10, tlTOneP9c11, tlTOneP9c12, tlTOneP9c2, tlTOneP9c3,
      tlTOneP9c4, tlTOneP9c5, tlTOneP9c6, tlTOneP9c7, tlTOneP9c8, tlTOneP9c9,
      tlTOneQ9c0, tlTOneQ9c1, tlTOneQ9c2, tlTOneQ9c3, tlTOneQ9c4, tlTOneQ9c5]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlTOne_s9 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP9c0 f ξ + tlTOneP9c1 f ξ) + (tlTOneP9c2 f ξ + tlTOneP9c3 f ξ)) +
        ((tlTOneP9c4 f ξ + tlTOneP9c5 f ξ) + (tlTOneP9c6 f ξ + tlTOneP9c7 f ξ))) +
        (((tlTOneP9c8 f ξ + tlTOneP9c9 f ξ) + (tlTOneP9c10 f ξ + tlTOneP9c11 f ξ)) +
        tlTOneP9c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlTOne_s9

#print axioms MazurTransfer.order27_certificate_tlTOne_s9


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP9c0 f ξ + tlTOneP9c1 f ξ) + (tlTOneP9c2 f ξ + tlTOneP9c3 f ξ)) +
        ((tlTOneP9c4 f ξ + tlTOneP9c5 f ξ) + (tlTOneP9c6 f ξ + tlTOneP9c7 f ξ))) +
        (((tlTOneP9c8 f ξ + tlTOneP9c9 f ξ) + (tlTOneP9c10 f ξ + tlTOneP9c11 f ξ)) +
        tlTOneP9c12 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlTOne_s9

#print axioms solution
