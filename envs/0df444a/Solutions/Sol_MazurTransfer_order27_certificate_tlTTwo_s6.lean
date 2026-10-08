-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:24:48.7475+00:00
-- url     : https://prove2.me/submissions/cca60313-9e2d-4ca5-9c75-55146cdff95f

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

lemma tlTTwo_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c0 f ξ + tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ) + (tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ)) +
        ((tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ) + (tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ))) +
        (tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ6c0 f ξ) * hT + (tlTTwoQ6c1 f ξ) * hT + (tlTTwoQ6c2 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c0, tlNSqP2c1, tlNSqP2c2, tlT0, tlT1, tlT2, tlT3, tlTTwoP6c0,
      tlTTwoP6c1, tlTTwoP6c2, tlTTwoP6c3, tlTTwoP6c4, tlTTwoP6c5, tlTTwoP6c6,
      tlTTwoP6c7, tlTTwoP6c8, tlTTwoP6c9, tlTTwoQ6c0, tlTTwoQ6c1, tlTTwoQ6c2]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlTTwo_s6 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c0 f ξ + tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ) + (tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ)) +
        ((tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ) + (tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ))) +
        (tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ)) := by
  exact MazurTorsion.Kubert.tlTTwo_s6

#print axioms MazurTransfer.order27_certificate_tlTTwo_s6


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c0 f ξ + tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ) + (tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ)) +
        ((tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ) + (tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ))) +
        (tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlTTwo_s6

#print axioms solution
