-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTOne_s2_tlTOne_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:25:04.730763+00:00
-- url     : https://prove2.me/submissions/ede82b20-5813-4428-8547-cb8faea7b913

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

lemma tlTOne_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP2c0 f ξ + tlTOneP2c1 f ξ) + (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ)) +
        ((tlTOneP2c4 f ξ + tlTOneP2c5 f ξ) + (tlTOneP2c6 f ξ + tlTOneP2c7 f ξ))) +
        ((tlTOneP2c8 f ξ + tlTOneP2c9 f ξ) + (tlTOneP2c10 f ξ + tlTOneP2c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlTOneQ2c0 f ξ) * hT + (tlTOneQ2c1 f ξ) * hT + (tlTOneQ2c2 f ξ) * hT + (tlTOneQ2c3 f ξ) * hT
  simp only [tlDSqP0c2, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP2c0,
      tlTOneP2c1, tlTOneP2c10, tlTOneP2c11, tlTOneP2c2, tlTOneP2c3, tlTOneP2c4,
      tlTOneP2c5, tlTOneP2c6, tlTOneP2c7, tlTOneP2c8, tlTOneP2c9, tlTOneQ2c0,
      tlTOneQ2c1, tlTOneQ2c2, tlTOneQ2c3]
  ring1

lemma tlTOne_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP3c0 f ξ + tlTOneP3c1 f ξ) + (tlTOneP3c2 f ξ + tlTOneP3c3 f ξ)) +
        ((tlTOneP3c4 f ξ + tlTOneP3c5 f ξ) + (tlTOneP3c6 f ξ + tlTOneP3c7 f ξ))) +
        (((tlTOneP3c8 f ξ + tlTOneP3c9 f ξ) + (tlTOneP3c10 f ξ + tlTOneP3c11 f ξ)) +
        tlTOneP3c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ3c0 f ξ) * hT + (tlTOneQ3c1 f ξ) * hT + (tlTOneQ3c2 f ξ) * hT + (tlTOneQ3c3 f ξ) * hT
      + (tlTOneQ3c4 f ξ) * hT
  simp only [tlDSqP0c3, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP3c0,
      tlTOneP3c1, tlTOneP3c10, tlTOneP3c11, tlTOneP3c12, tlTOneP3c2, tlTOneP3c3,
      tlTOneP3c4, tlTOneP3c5, tlTOneP3c6, tlTOneP3c7, tlTOneP3c8, tlTOneP3c9,
      tlTOneQ3c0, tlTOneQ3c1, tlTOneQ3c2, tlTOneQ3c3, tlTOneQ3c4]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlTOne_s2_tlTOne_s3 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP2c0 f ξ + tlTOneP2c1 f ξ) + (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ)) +
        ((tlTOneP2c4 f ξ + tlTOneP2c5 f ξ) + (tlTOneP2c6 f ξ + tlTOneP2c7 f ξ))) +
        ((tlTOneP2c8 f ξ + tlTOneP2c9 f ξ) + (tlTOneP2c10 f ξ + tlTOneP2c11 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP3c0 f ξ + tlTOneP3c1 f ξ) + (tlTOneP3c2 f ξ + tlTOneP3c3 f ξ)) +
        ((tlTOneP3c4 f ξ + tlTOneP3c5 f ξ) + (tlTOneP3c6 f ξ + tlTOneP3c7 f ξ))) +
        (((tlTOneP3c8 f ξ + tlTOneP3c9 f ξ) + (tlTOneP3c10 f ξ + tlTOneP3c11 f ξ)) +
        tlTOneP3c12 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlTOne_s2, MazurTorsion.Kubert.tlTOne_s3⟩

#print axioms MazurTransfer.order27_certificate_tlTOne_s2_tlTOne_s3


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP2c0 f ξ + tlTOneP2c1 f ξ) + (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ)) +
        ((tlTOneP2c4 f ξ + tlTOneP2c5 f ξ) + (tlTOneP2c6 f ξ + tlTOneP2c7 f ξ))) +
        ((tlTOneP2c8 f ξ + tlTOneP2c9 f ξ) + (tlTOneP2c10 f ξ + tlTOneP2c11 f ξ)))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP3c0 f ξ + tlTOneP3c1 f ξ) + (tlTOneP3c2 f ξ + tlTOneP3c3 f ξ)) +
        ((tlTOneP3c4 f ξ + tlTOneP3c5 f ξ) + (tlTOneP3c6 f ξ + tlTOneP3c7 f ξ))) +
        (((tlTOneP3c8 f ξ + tlTOneP3c9 f ξ) + (tlTOneP3c10 f ξ + tlTOneP3c11 f ξ)) +
        tlTOneP3c12 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlTOne_s2_tlTOne_s3

#print axioms solution
