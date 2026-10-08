-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:13.611544+00:00
-- url     : https://prove2.me/submissions/d7b4c2af-9c9d-4959-aa6d-8a73c8735c61

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

lemma tlWOneX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ +
      tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ +
      tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ +
      tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ) + (tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ)) +
        ((tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ) + (tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ))) +
        (((tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ) + (tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ)) +
        ((tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ))))
        + ((tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ) + (tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ))
        := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP5c10, tlTOneP5c11, tlTOneP5c12,
      tlTOneP5c6, tlTOneP5c7, tlTOneP5c8, tlTOneP5c9, tlTOneP6c0, tlTOneP6c1,
      tlTOneP6c10, tlTOneP6c11, tlTOneP6c12, tlTOneP6c2, tlTOneP6c3, tlTOneP6c4,
      tlTOneP6c5, tlTOneP6c6, tlTOneP6c7, tlTOneP6c8, tlTOneP6c9, tlWOneXP3c0,
      tlWOneXP3c1, tlWOneXP3c10, tlWOneXP3c11, tlWOneXP3c12, tlWOneXP3c13,
      tlWOneXP3c14, tlWOneXP3c15, tlWOneXP3c16, tlWOneXP3c17, tlWOneXP3c18,
      tlWOneXP3c19, tlWOneXP3c2, tlWOneXP3c3, tlWOneXP3c4, tlWOneXP3c5, tlWOneXP3c6,
      tlWOneXP3c7, tlWOneXP3c8, tlWOneXP3c9]
  ring1

lemma tlWOneX_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ +
      tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP4c0 f + tlWOneXP4c1 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ)) +
        ((tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ))) +
        (((tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ) + (tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ)) +
        ((tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ) + (tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ))))
        + (((tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ) + (tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ))
        + tlWOneXP4c20 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP7c0, tlTOneP7c1, tlTOneP7c10,
      tlTOneP7c11, tlTOneP7c12, tlTOneP7c2, tlTOneP7c3, tlTOneP7c4, tlTOneP7c5,
      tlTOneP7c6, tlTOneP7c7, tlTOneP7c8, tlTOneP7c9, tlTOneP8c0, tlTOneP8c1,
      tlTOneP8c2, tlTOneP8c3, tlTOneP8c4, tlTOneP8c5, tlTOneP8c6, tlWOneXP4c0,
      tlWOneXP4c1, tlWOneXP4c10, tlWOneXP4c11, tlWOneXP4c12, tlWOneXP4c13,
      tlWOneXP4c14, tlWOneXP4c15, tlWOneXP4c16, tlWOneXP4c17, tlWOneXP4c18,
      tlWOneXP4c19, tlWOneXP4c2, tlWOneXP4c20, tlWOneXP4c3, tlWOneXP4c4,
      tlWOneXP4c5, tlWOneXP4c6, tlWOneXP4c7, tlWOneXP4c8, tlWOneXP4c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ +
      tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ +
      tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ +
      tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ) + (tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ)) +
        ((tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ) + (tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ))) +
        (((tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ) + (tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ)) +
        ((tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ))))
        + ((tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ) + (tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ +
      tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP4c0 f + tlWOneXP4c1 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ)) +
        ((tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ))) +
        (((tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ) + (tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ)) +
        ((tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ) + (tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ))))
        + (((tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ) + (tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ))
        + tlWOneXP4c20 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlWOneX_s3, MazurTorsion.Kubert.tlWOneX_s4⟩

#print axioms MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ +
      tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ +
      tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ +
      tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ) + (tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ)) +
        ((tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ) + (tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ))) +
        (((tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ) + (tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ)) +
        ((tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ))))
        + ((tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ) + (tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ +
      tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP4c0 f + tlWOneXP4c1 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ)) +
        ((tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ))) +
        (((tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ) + (tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ)) +
        ((tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ) + (tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ))))
        + (((tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ) + (tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ))
        + tlWOneXP4c20 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlWOneX_s3_tlWOneX_s4

#print axioms solution
