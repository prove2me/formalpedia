-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWZeroX_s0_tlWZeroX_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:21.760363+00:00
-- url     : https://prove2.me/submissions/6f963f9a-dac0-46c8-a15a-80a5478551b7

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

lemma tlWZeroX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1
      f ξ + tlDCbP1c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ))
        + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f
        ξ)))) + tlWZeroXP0c16 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP0c0, tlDCbP0c1, tlDCbP0c2, tlDCbP0c3, tlDCbP0c4, tlDCbP0c5, tlDCbP0c6,
      tlDCbP0c7, tlDCbP0c8, tlDCbP0c9, tlDCbP1c0, tlDCbP1c1, tlDCbP1c2, tlMZeroV0,
      tlT0, tlT1, tlT2, tlT3, tlWZeroXP0c0, tlWZeroXP0c1, tlWZeroXP0c10,
      tlWZeroXP0c11, tlWZeroXP0c12, tlWZeroXP0c13, tlWZeroXP0c14, tlWZeroXP0c15,
      tlWZeroXP0c16, tlWZeroXP0c2, tlWZeroXP0c3, tlWZeroXP0c4, tlWZeroXP0c5,
      tlWZeroXP0c6, tlWZeroXP0c7, tlWZeroXP0c8, tlWZeroXP0c9]
  ring1

lemma tlWZeroX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ
      + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP2c0 f ξ +
      tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ) + (tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ)) +
        ((tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ) + (tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ))) +
        (((tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ) + (tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ))
        + ((tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ) + (tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f
        ξ)))) + ((tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ) + tlWZeroXP1c18 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP1c10, tlDCbP1c11, tlDCbP1c12, tlDCbP1c3, tlDCbP1c4, tlDCbP1c5, tlDCbP1c6,
      tlDCbP1c7, tlDCbP1c8, tlDCbP1c9, tlDCbP2c0, tlDCbP2c1, tlDCbP2c2, tlMZeroV0,
      tlT0, tlT1, tlT2, tlT3, tlWZeroXP1c0, tlWZeroXP1c1, tlWZeroXP1c10,
      tlWZeroXP1c11, tlWZeroXP1c12, tlWZeroXP1c13, tlWZeroXP1c14, tlWZeroXP1c15,
      tlWZeroXP1c16, tlWZeroXP1c17, tlWZeroXP1c18, tlWZeroXP1c2, tlWZeroXP1c3,
      tlWZeroXP1c4, tlWZeroXP1c5, tlWZeroXP1c6, tlWZeroXP1c7, tlWZeroXP1c8,
      tlWZeroXP1c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWZeroX_s0_tlWZeroX_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1
      f ξ + tlDCbP1c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ))
        + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f
        ξ)))) + tlWZeroXP0c16 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ
      + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP2c0 f ξ +
      tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ) + (tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ)) +
        ((tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ) + (tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ))) +
        (((tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ) + (tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ))
        + ((tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ) + (tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f
        ξ)))) + ((tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ) + tlWZeroXP1c18 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlWZeroX_s0, MazurTorsion.Kubert.tlWZeroX_s1⟩

#print axioms MazurTransfer.order27_certificate_tlWZeroX_s0_tlWZeroX_s1


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1
      f ξ + tlDCbP1c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ))
        + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f
        ξ)))) + tlWZeroXP0c16 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ
      + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP2c0 f ξ +
      tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ) + (tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ)) +
        ((tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ) + (tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ))) +
        (((tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ) + (tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ))
        + ((tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ) + (tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f
        ξ)))) + ((tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ) + tlWZeroXP1c18 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlWZeroX_s0_tlWZeroX_s1

#print axioms solution
