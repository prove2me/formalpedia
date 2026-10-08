-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlDSq_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:25:00.643486+00:00
-- url     : https://prove2.me/submissions/516665a3-f742-4874-aa34-eddf902e7780

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

lemma tlDSq_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ) := by
  linear_combination (norm := skip)
    (tlDSqQ0c0 f ξ) * hT + (tlDSqQ0c1 f ξ) * hT + (tlDSqQ0c2 f ξ) * hT + (tlDSqQ0c3 f ξ) * hT
  simp only [tlD0, tlD1, tlDSqP0c0, tlDSqP0c1, tlDSqP0c2, tlDSqP0c3, tlDSqP0c4, tlDSqP0c5,
      tlDSqP0c6, tlDSqP0c7, tlDSqP0c8, tlDSqP0c9, tlDSqQ0c0, tlDSqQ0c1, tlDSqQ0c2,
      tlDSqQ0c3, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlDSq_s0 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ)) := by
  exact MazurTorsion.Kubert.tlDSq_s0

#print axioms MazurTransfer.order27_certificate_tlDSq_s0


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlDSq_s0

#print axioms solution
