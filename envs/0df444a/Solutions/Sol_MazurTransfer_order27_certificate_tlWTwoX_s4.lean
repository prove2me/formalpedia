-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWTwoX_s4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:24:58.971808+00:00
-- url     : https://prove2.me/submissions/98658e5e-23c6-4484-bc72-444919969dd8

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

lemma tlWTwoX_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP13c9 f ξ + tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ + tlTTwoP13c12 f ξ) * tlMTwoV0 f =
      ((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP13c10, tlTTwoP13c11, tlTTwoP13c12,
      tlTTwoP13c9, tlWTwoXP4c0, tlWTwoXP4c1, tlWTwoXP4c2, tlWTwoXP4c3, tlWTwoXP4c4,
      tlWTwoXP4c5, tlWTwoXP4c6]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWTwoX_s4 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP13c9 f ξ + tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ + tlTTwoP13c12 f ξ) * tlMTwoV0 f =
      ((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ)) := by
  exact MazurTorsion.Kubert.tlWTwoX_s4

#print axioms MazurTransfer.order27_certificate_tlWTwoX_s4


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP13c9 f ξ + tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ + tlTTwoP13c12 f ξ) * tlMTwoV0 f =
      ((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s4

#print axioms solution
