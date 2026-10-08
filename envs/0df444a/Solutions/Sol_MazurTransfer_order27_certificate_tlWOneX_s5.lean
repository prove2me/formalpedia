-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWOneX_s5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:16.013075+00:00
-- url     : https://prove2.me/submissions/35effd68-38cd-4631-9a57-a91b5842d347

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

lemma tlWOneX_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ +
      tlTOneP8c12 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ) * tlMOneV0 f =
      ((((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ)) +
        ((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ))) +
        (((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ)) +
        ((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ))))
        + (((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ))
        + tlWOneXP5c20 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP8c10, tlTOneP8c11, tlTOneP8c12,
      tlTOneP8c7, tlTOneP8c8, tlTOneP8c9, tlTOneP9c0, tlTOneP9c1, tlTOneP9c10,
      tlTOneP9c11, tlTOneP9c12, tlTOneP9c2, tlTOneP9c3, tlTOneP9c4, tlTOneP9c5,
      tlTOneP9c6, tlTOneP9c7, tlTOneP9c8, tlTOneP9c9, tlWOneXP5c0, tlWOneXP5c1,
      tlWOneXP5c10, tlWOneXP5c11, tlWOneXP5c12, tlWOneXP5c13, tlWOneXP5c14,
      tlWOneXP5c15, tlWOneXP5c16, tlWOneXP5c17, tlWOneXP5c18, tlWOneXP5c19,
      tlWOneXP5c2, tlWOneXP5c20, tlWOneXP5c3, tlWOneXP5c4, tlWOneXP5c5, tlWOneXP5c6,
      tlWOneXP5c7, tlWOneXP5c8, tlWOneXP5c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWOneX_s5 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ +
      tlTOneP8c12 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ) * tlMOneV0 f =
      ((((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ)) +
        ((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ))) +
        (((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ)) +
        ((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ))))
        + (((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ))
        + tlWOneXP5c20 f ξ)) := by
  exact MazurTorsion.Kubert.tlWOneX_s5

#print axioms MazurTransfer.order27_certificate_tlWOneX_s5


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ +
      tlTOneP8c12 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ) * tlMOneV0 f =
      ((((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ)) +
        ((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ))) +
        (((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ)) +
        ((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ))))
        + (((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ))
        + tlWOneXP5c20 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlWOneX_s5

#print axioms solution
