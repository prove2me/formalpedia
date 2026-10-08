-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:23.699895+00:00
-- url     : https://prove2.me/submissions/c96f852e-f3d4-452e-98a3-581c60a35cfd

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

lemma tlWZeroX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ
      + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ +
      tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ)) +
        ((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ))) +
        (((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ))
        + ((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)))) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ)) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP2c10, tlDCbP2c11, tlDCbP2c12, tlDCbP2c13, tlDCbP2c3, tlDCbP2c4, tlDCbP2c5,
      tlDCbP2c6, tlDCbP2c7, tlDCbP2c8, tlDCbP2c9, tlDCbP3c0, tlDCbP3c1, tlMZeroV0,
      tlT0, tlT1, tlT2, tlT3, tlWZeroXP2c0, tlWZeroXP2c1, tlWZeroXP2c10,
      tlWZeroXP2c11, tlWZeroXP2c12, tlWZeroXP2c13, tlWZeroXP2c14, tlWZeroXP2c15,
      tlWZeroXP2c16, tlWZeroXP2c17, tlWZeroXP2c18, tlWZeroXP2c19, tlWZeroXP2c2,
      tlWZeroXP2c3, tlWZeroXP2c4, tlWZeroXP2c5, tlWZeroXP2c6, tlWZeroXP2c7,
      tlWZeroXP2c8, tlWZeroXP2c9]
  ring1

lemma tlWZeroX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ + tlDCbP3c4 f ξ + tlDCbP3c5 f ξ + tlDCbP3c6 f ξ + tlDCbP3c7 f ξ
      + tlDCbP3c8 f ξ + tlDCbP3c9 f ξ + tlDCbP3c10 f ξ + tlDCbP3c11 f ξ) * tlMZeroV0 f =
      (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ))
        + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f
        ξ))) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP3c10, tlDCbP3c11, tlDCbP3c2, tlDCbP3c3, tlDCbP3c4, tlDCbP3c5, tlDCbP3c6,
      tlDCbP3c7, tlDCbP3c8, tlDCbP3c9, tlMZeroV0, tlT0, tlT1, tlT2, tlT3,
      tlWZeroXP3c0, tlWZeroXP3c1, tlWZeroXP3c10, tlWZeroXP3c11, tlWZeroXP3c12,
      tlWZeroXP3c13, tlWZeroXP3c14, tlWZeroXP3c15, tlWZeroXP3c2, tlWZeroXP3c3,
      tlWZeroXP3c4, tlWZeroXP3c5, tlWZeroXP3c6, tlWZeroXP3c7, tlWZeroXP3c8,
      tlWZeroXP3c9]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ
      + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ +
      tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ)) +
        ((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ))) +
        (((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ))
        + ((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)))) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP3c2 f ξ + tlDCbP3c3 f ξ + tlDCbP3c4 f ξ + tlDCbP3c5 f ξ + tlDCbP3c6 f ξ + tlDCbP3c7 f ξ
      + tlDCbP3c8 f ξ + tlDCbP3c9 f ξ + tlDCbP3c10 f ξ + tlDCbP3c11 f ξ) * tlMZeroV0 f =
      (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ))
        + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f
        ξ)))) := by
  exact ⟨MazurTorsion.Kubert.tlWZeroX_s2, MazurTorsion.Kubert.tlWZeroX_s3⟩

#print axioms MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ
      + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ +
      tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ)) +
        ((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ))) +
        (((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ))
        + ((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)))) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDCbP3c2 f ξ + tlDCbP3c3 f ξ + tlDCbP3c4 f ξ + tlDCbP3c5 f ξ + tlDCbP3c6 f ξ + tlDCbP3c7 f ξ
      + tlDCbP3c8 f ξ + tlDCbP3c9 f ξ + tlDCbP3c10 f ξ + tlDCbP3c11 f ξ) * tlMZeroV0 f =
      (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ))
        + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f
        ξ))))  := by
  exact MazurTransfer.order27_certificate_tlWZeroX_s2_tlWZeroX_s3

#print axioms solution
