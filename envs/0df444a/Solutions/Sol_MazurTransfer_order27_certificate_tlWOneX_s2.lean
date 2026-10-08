-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWOneX_s2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:11.723387+00:00
-- url     : https://prove2.me/submissions/8fbec0ce-70f2-42b2-bbff-85e2a4b174f1

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

lemma tlWOneX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ +
      tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ +
      tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
      tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ +
      tlTOneP5c5 f ξ) * tlMOneV0 f =
      ((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ))))
        + ((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + tlWOneXP2c18 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP3c11, tlTOneP3c12, tlTOneP4c0,
      tlTOneP4c1, tlTOneP4c10, tlTOneP4c11, tlTOneP4c12, tlTOneP4c2, tlTOneP4c3,
      tlTOneP4c4, tlTOneP4c5, tlTOneP4c6, tlTOneP4c7, tlTOneP4c8, tlTOneP4c9,
      tlTOneP5c0, tlTOneP5c1, tlTOneP5c2, tlTOneP5c3, tlTOneP5c4, tlTOneP5c5,
      tlWOneXP2c0, tlWOneXP2c1, tlWOneXP2c10, tlWOneXP2c11, tlWOneXP2c12,
      tlWOneXP2c13, tlWOneXP2c14, tlWOneXP2c15, tlWOneXP2c16, tlWOneXP2c17,
      tlWOneXP2c18, tlWOneXP2c2, tlWOneXP2c3, tlWOneXP2c4, tlWOneXP2c5, tlWOneXP2c6,
      tlWOneXP2c7, tlWOneXP2c8, tlWOneXP2c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWOneX_s2 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ +
      tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ +
      tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
      tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ +
      tlTOneP5c5 f ξ) * tlMOneV0 f =
      ((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ))))
        + ((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + tlWOneXP2c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlWOneX_s2

#print axioms MazurTransfer.order27_certificate_tlWOneX_s2


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ +
      tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ +
      tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
      tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ +
      tlTOneP5c5 f ξ) * tlMOneV0 f =
      ((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ))))
        + ((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + tlWOneXP2c18 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlWOneX_s2

#print axioms solution
