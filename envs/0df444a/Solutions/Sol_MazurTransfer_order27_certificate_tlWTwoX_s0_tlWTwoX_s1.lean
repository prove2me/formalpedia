-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:24:55.362989+00:00
-- url     : https://prove2.me/submissions/c78da662-d77d-47cb-957a-d3fed64c706c

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

lemma tlWTwoX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ +
      tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ +
      tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ +
      tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ +
      tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ))))
        + (((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ))
        + tlWTwoXP0c20 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP0c0, tlTTwoP0c1, tlTTwoP0c2,
      tlTTwoP0c3, tlTTwoP0c4, tlTTwoP0c5, tlTTwoP0c6, tlTTwoP0c7, tlTTwoP0c8,
      tlTTwoP0c9, tlTTwoP1c0, tlTTwoP1c1, tlTTwoP1c10, tlTTwoP1c11, tlTTwoP1c12,
      tlTTwoP1c2, tlTTwoP1c3, tlTTwoP1c4, tlTTwoP1c5, tlTTwoP1c6, tlTTwoP1c7,
      tlTTwoP1c8, tlTTwoP1c9, tlTTwoP2c0, tlTTwoP2c1, tlTTwoP2c10, tlTTwoP2c11,
      tlTTwoP2c12, tlTTwoP2c13, tlTTwoP2c14, tlTTwoP2c15, tlTTwoP2c2, tlTTwoP2c3,
      tlTTwoP2c4, tlTTwoP2c5, tlTTwoP2c6, tlTTwoP2c7, tlTTwoP2c8, tlTTwoP2c9,
      tlTTwoP3c0, tlTTwoP3c1, tlTTwoP3c2, tlTTwoP3c3, tlTTwoP3c4, tlTTwoP3c5,
      tlWTwoXP0c0, tlWTwoXP0c1, tlWTwoXP0c10, tlWTwoXP0c11, tlWTwoXP0c12,
      tlWTwoXP0c13, tlWTwoXP0c14, tlWTwoXP0c15, tlWTwoXP0c16, tlWTwoXP0c17,
      tlWTwoXP0c18, tlWTwoXP0c19, tlWTwoXP0c2, tlWTwoXP0c20, tlWTwoXP0c3,
      tlWTwoXP0c4, tlWTwoXP0c5, tlWTwoXP0c6, tlWTwoXP0c7, tlWTwoXP0c8, tlWTwoXP0c9]
  ring1

lemma tlWTwoX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ +
      tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ +
      tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
      tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ +
      tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ +
      tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ +
      tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ +
      tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ +
      tlTTwoP7c1 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ) + (tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ)) +
        ((tlWTwoXP1c4 f ξ + tlWTwoXP1c5 f ξ) + (tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ))) +
        (((tlWTwoXP1c8 f ξ + tlWTwoXP1c9 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ)) +
        ((tlWTwoXP1c12 f ξ + tlWTwoXP1c13 f ξ) + (tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ))))
        + (((tlWTwoXP1c16 f ξ + tlWTwoXP1c17 f ξ) + (tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ))
        + (tlWTwoXP1c20 f ξ + tlWTwoXP1c21 f ξ)) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP3c10, tlTTwoP3c11, tlTTwoP3c6,
      tlTTwoP3c7, tlTTwoP3c8, tlTTwoP3c9, tlTTwoP4c0, tlTTwoP4c1, tlTTwoP4c10,
      tlTTwoP4c11, tlTTwoP4c12, tlTTwoP4c13, tlTTwoP4c2, tlTTwoP4c3, tlTTwoP4c4,
      tlTTwoP4c5, tlTTwoP4c6, tlTTwoP4c7, tlTTwoP4c8, tlTTwoP4c9, tlTTwoP5c0,
      tlTTwoP5c1, tlTTwoP5c10, tlTTwoP5c11, tlTTwoP5c12, tlTTwoP5c13, tlTTwoP5c2,
      tlTTwoP5c3, tlTTwoP5c4, tlTTwoP5c5, tlTTwoP5c6, tlTTwoP5c7, tlTTwoP5c8,
      tlTTwoP5c9, tlTTwoP6c0, tlTTwoP6c1, tlTTwoP6c2, tlTTwoP6c3, tlTTwoP6c4,
      tlTTwoP6c5, tlTTwoP6c6, tlTTwoP6c7, tlTTwoP6c8, tlTTwoP6c9, tlTTwoP7c0,
      tlTTwoP7c1, tlWTwoXP1c0, tlWTwoXP1c1, tlWTwoXP1c10, tlWTwoXP1c11,
      tlWTwoXP1c12, tlWTwoXP1c13, tlWTwoXP1c14, tlWTwoXP1c15, tlWTwoXP1c16,
      tlWTwoXP1c17, tlWTwoXP1c18, tlWTwoXP1c19, tlWTwoXP1c2, tlWTwoXP1c20,
      tlWTwoXP1c21, tlWTwoXP1c3, tlWTwoXP1c4, tlWTwoXP1c5, tlWTwoXP1c6, tlWTwoXP1c7,
      tlWTwoXP1c8, tlWTwoXP1c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ +
      tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ +
      tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ +
      tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ +
      tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ))))
        + (((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ))
        + tlWTwoXP0c20 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ +
      tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ +
      tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
      tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ +
      tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ +
      tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ +
      tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ +
      tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ +
      tlTTwoP7c1 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ) + (tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ)) +
        ((tlWTwoXP1c4 f ξ + tlWTwoXP1c5 f ξ) + (tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ))) +
        (((tlWTwoXP1c8 f ξ + tlWTwoXP1c9 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ)) +
        ((tlWTwoXP1c12 f ξ + tlWTwoXP1c13 f ξ) + (tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ))))
        + (((tlWTwoXP1c16 f ξ + tlWTwoXP1c17 f ξ) + (tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ))
        + (tlWTwoXP1c20 f ξ + tlWTwoXP1c21 f ξ))) := by
  exact ⟨MazurTorsion.Kubert.tlWTwoX_s0, MazurTorsion.Kubert.tlWTwoX_s1⟩

#print axioms MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ +
      tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ +
      tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ +
      tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ +
      tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) *
      tlMTwoV0 f =
      ((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ))))
        + (((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ))
        + tlWTwoXP0c20 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ +
      tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ +
      tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
      tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ +
      tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ +
      tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ +
      tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ +
      tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ +
      tlTTwoP7c1 f ξ) * tlMTwoV0 f =
      ((((tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ) + (tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ)) +
        ((tlWTwoXP1c4 f ξ + tlWTwoXP1c5 f ξ) + (tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ))) +
        (((tlWTwoXP1c8 f ξ + tlWTwoXP1c9 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ)) +
        ((tlWTwoXP1c12 f ξ + tlWTwoXP1c13 f ξ) + (tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ))))
        + (((tlWTwoXP1c16 f ξ + tlWTwoXP1c17 f ξ) + (tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ))
        + (tlWTwoXP1c20 f ξ + tlWTwoXP1c21 f ξ)))  := by
  exact MazurTransfer.order27_certificate_tlWTwoX_s0_tlWTwoX_s1

#print axioms solution
