-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:25:02.745751+00:00
-- url     : https://prove2.me/submissions/2b009e6c-e32b-4451-a09c-2cadb9421722

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

lemma tlTOne_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        tlTOneP0c8 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ0c0 f ξ) * hT + (tlTOneQ0c1 f ξ) * hT
  simp only [tlDSqP0c0, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP0c0,
      tlTOneP0c1, tlTOneP0c2, tlTOneP0c3, tlTOneP0c4, tlTOneP0c5, tlTOneP0c6,
      tlTOneP0c7, tlTOneP0c8, tlTOneQ0c0, tlTOneQ0c1]
  ring1

lemma tlTOne_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP1c0 f ξ + tlTOneP1c1 f ξ) + (tlTOneP1c2 f ξ + tlTOneP1c3 f ξ)) +
        ((tlTOneP1c4 f ξ + tlTOneP1c5 f ξ) + (tlTOneP1c6 f ξ + tlTOneP1c7 f ξ))) +
        (tlTOneP1c8 f ξ + tlTOneP1c9 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ1c0 f ξ) * hT + (tlTOneQ1c1 f ξ) * hT + (tlTOneQ1c2 f ξ) * hT
  simp only [tlDSqP0c1, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP1c0,
      tlTOneP1c1, tlTOneP1c2, tlTOneP1c3, tlTOneP1c4, tlTOneP1c5, tlTOneP1c6,
      tlTOneP1c7, tlTOneP1c8, tlTOneP1c9, tlTOneQ1c0, tlTOneQ1c1, tlTOneQ1c2]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        tlTOneP0c8 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP1c0 f ξ + tlTOneP1c1 f ξ) + (tlTOneP1c2 f ξ + tlTOneP1c3 f ξ)) +
        ((tlTOneP1c4 f ξ + tlTOneP1c5 f ξ) + (tlTOneP1c6 f ξ + tlTOneP1c7 f ξ))) +
        (tlTOneP1c8 f ξ + tlTOneP1c9 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlTOne_s0, MazurTorsion.Kubert.tlTOne_s1⟩

#print axioms MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        tlTOneP0c8 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP1c0 f ξ + tlTOneP1c1 f ξ) + (tlTOneP1c2 f ξ + tlTOneP1c3 f ξ)) +
        ((tlTOneP1c4 f ξ + tlTOneP1c5 f ξ) + (tlTOneP1c6 f ξ + tlTOneP1c7 f ξ))) +
        (tlTOneP1c8 f ξ + tlTOneP1c9 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlTOne_s0_tlTOne_s1

#print axioms solution
