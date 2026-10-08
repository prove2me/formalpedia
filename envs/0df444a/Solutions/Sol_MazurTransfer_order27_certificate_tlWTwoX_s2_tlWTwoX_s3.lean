-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:24:57.18134+00:00
-- url     : https://prove2.me/submissions/3b3f4331-8a4d-40c6-b695-e5c54cddd2cb

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

lemma tlWTwoX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ +
      tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ +
      tlTTwoP7c12 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ +
      tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ +
      tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ +
      tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ +
      tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ +
      tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP9c14 f ξ +
      tlTTwoP9c15 f ξ + tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ) + (tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ)) +
        ((tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ) + (tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ))) +
        (((tlWTwoXP2c8 f ξ + tlWTwoXP2c9 f ξ) + (tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ)) +
        ((tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ) + (tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ))))
        + (((tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ) + (tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ))
        + ((tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ) + tlWTwoXP2c22 f ξ)) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP10c0, tlTTwoP10c1, tlTTwoP7c10,
      tlTTwoP7c11, tlTTwoP7c12, tlTTwoP7c2, tlTTwoP7c3, tlTTwoP7c4, tlTTwoP7c5,
      tlTTwoP7c6, tlTTwoP7c7, tlTTwoP7c8, tlTTwoP7c9, tlTTwoP8c0, tlTTwoP8c1,
      tlTTwoP8c10, tlTTwoP8c11, tlTTwoP8c12, tlTTwoP8c13, tlTTwoP8c2, tlTTwoP8c3,
      tlTTwoP8c4, tlTTwoP8c5, tlTTwoP8c6, tlTTwoP8c7, tlTTwoP8c8, tlTTwoP8c9,
      tlTTwoP9c0, tlTTwoP9c1, tlTTwoP9c10, tlTTwoP9c11, tlTTwoP9c12, tlTTwoP9c13,
      tlTTwoP9c14, tlTTwoP9c15, tlTTwoP9c16, tlTTwoP9c17, tlTTwoP9c2, tlTTwoP9c3,
      tlTTwoP9c4, tlTTwoP9c5, tlTTwoP9c6, tlTTwoP9c7, tlTTwoP9c8, tlTTwoP9c9,
      tlWTwoXP2c0, tlWTwoXP2c1, tlWTwoXP2c10, tlWTwoXP2c11, tlWTwoXP2c12,
      tlWTwoXP2c13, tlWTwoXP2c14, tlWTwoXP2c15, tlWTwoXP2c16, tlWTwoXP2c17,
      tlWTwoXP2c18, tlWTwoXP2c19, tlWTwoXP2c2, tlWTwoXP2c20, tlWTwoXP2c21,
      tlWTwoXP2c22, tlWTwoXP2c3, tlWTwoXP2c4, tlWTwoXP2c5, tlWTwoXP2c6, tlWTwoXP2c7,
      tlWTwoXP2c8, tlWTwoXP2c9]
  ring1

lemma tlWTwoX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ +
      tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ +
      tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ +
      tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ +
      tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP12c0 f ξ
      + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ +
      tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ + tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ +
      tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ + tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ + tlTTwoP13c6 f ξ +
      tlTTwoP13c7 f ξ + tlTTwoP13c8 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ) + (tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ)) +
        ((tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ) + (tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ))) +
        (((tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ) + (tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ)) +
        ((tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ) + (tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ))))
        + (((tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ) + (tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ))
        + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ)) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP10c10, tlTTwoP10c11, tlTTwoP10c2,
      tlTTwoP10c3, tlTTwoP10c4, tlTTwoP10c5, tlTTwoP10c6, tlTTwoP10c7, tlTTwoP10c8,
      tlTTwoP10c9, tlTTwoP11c0, tlTTwoP11c1, tlTTwoP11c10, tlTTwoP11c11,
      tlTTwoP11c12, tlTTwoP11c13, tlTTwoP11c2, tlTTwoP11c3, tlTTwoP11c4,
      tlTTwoP11c5, tlTTwoP11c6, tlTTwoP11c7, tlTTwoP11c8, tlTTwoP11c9, tlTTwoP12c0,
      tlTTwoP12c1, tlTTwoP12c10, tlTTwoP12c11, tlTTwoP12c12, tlTTwoP12c13,
      tlTTwoP12c2, tlTTwoP12c3, tlTTwoP12c4, tlTTwoP12c5, tlTTwoP12c6, tlTTwoP12c7,
      tlTTwoP12c8, tlTTwoP12c9, tlTTwoP13c0, tlTTwoP13c1, tlTTwoP13c2, tlTTwoP13c3,
      tlTTwoP13c4, tlTTwoP13c5, tlTTwoP13c6, tlTTwoP13c7, tlTTwoP13c8, tlWTwoXP3c0,
      tlWTwoXP3c1, tlWTwoXP3c10, tlWTwoXP3c11, tlWTwoXP3c12, tlWTwoXP3c13,
      tlWTwoXP3c14, tlWTwoXP3c15, tlWTwoXP3c16, tlWTwoXP3c17, tlWTwoXP3c18,
      tlWTwoXP3c19, tlWTwoXP3c2, tlWTwoXP3c20, tlWTwoXP3c21, tlWTwoXP3c3,
      tlWTwoXP3c4, tlWTwoXP3c5, tlWTwoXP3c6, tlWTwoXP3c7, tlWTwoXP3c8, tlWTwoXP3c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ +
      tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ +
      tlTTwoP7c12 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ +
      tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ +
      tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ +
      tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ +
      tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ +
      tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP9c14 f ξ +
      tlTTwoP9c15 f ξ + tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ) + (tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ)) +
        ((tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ) + (tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ))) +
        (((tlWTwoXP2c8 f ξ + tlWTwoXP2c9 f ξ) + (tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ)) +
        ((tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ) + (tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ))))
        + (((tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ) + (tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ))
        + ((tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ) + tlWTwoXP2c22 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ +
      tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ +
      tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ +
      tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ +
      tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP12c0 f ξ
      + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ +
      tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ + tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ +
      tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ + tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ + tlTTwoP13c6 f ξ +
      tlTTwoP13c7 f ξ + tlTTwoP13c8 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ) + (tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ)) +
        ((tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ) + (tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ))) +
        (((tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ) + (tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ)) +
        ((tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ) + (tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ))))
        + (((tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ) + (tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ))
        + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) := by
  exact ⟨MazurTorsion.Kubert.tlWTwoX_s2, MazurTorsion.Kubert.tlWTwoX_s3⟩

#print axioms MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ +
      tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ +
      tlTTwoP7c12 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ +
      tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ +
      tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ +
      tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ +
      tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ +
      tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP9c14 f ξ +
      tlTTwoP9c15 f ξ + tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ) + (tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ)) +
        ((tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ) + (tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ))) +
        (((tlWTwoXP2c8 f ξ + tlWTwoXP2c9 f ξ) + (tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ)) +
        ((tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ) + (tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ))))
        + (((tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ) + (tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ))
        + ((tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ) + tlWTwoXP2c22 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ +
      tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ +
      tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ +
      tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ +
      tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP12c0 f ξ
      + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ +
      tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ + tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ +
      tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ + tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ + tlTTwoP13c6 f ξ +
      tlTTwoP13c7 f ξ + tlTTwoP13c8 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ) + (tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ)) +
        ((tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ) + (tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ))) +
        (((tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ) + (tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ)) +
        ((tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ) + (tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ))))
        + (((tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ) + (tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ))
        + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ)))  := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s2_tlWTwoX_s3

#print axioms solution
