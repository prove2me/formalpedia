-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s30_tlNCb_s31
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:23:38.878932+00:00
-- url     : https://prove2.me/submissions/4bbab0da-022c-4827-8f3a-f011026b405c

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

lemma tlNCb_s30 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) +
        ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) +
        (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        tlNCbP30c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ30c0 f ξ) * hT + (tlNCbQ30c1 f ξ) * hT + (tlNCbQ30c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP30c0, tlNCbP30c1, tlNCbP30c10, tlNCbP30c11,
      tlNCbP30c12, tlNCbP30c2, tlNCbP30c3, tlNCbP30c4, tlNCbP30c5, tlNCbP30c6,
      tlNCbP30c7, tlNCbP30c8, tlNCbP30c9, tlNCbQ30c0, tlNCbQ30c1, tlNCbQ30c2,
      tlNSqP3c1, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s31 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP31c0 f ξ + tlNCbP31c1 f ξ) + (tlNCbP31c2 f ξ + tlNCbP31c3 f ξ)) +
        ((tlNCbP31c4 f ξ + tlNCbP31c5 f ξ) + (tlNCbP31c6 f ξ + tlNCbP31c7 f ξ))) +
        (((tlNCbP31c8 f ξ + tlNCbP31c9 f ξ) + (tlNCbP31c10 f ξ + tlNCbP31c11 f ξ)) +
        (tlNCbP31c12 f ξ + tlNCbP31c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ31c0 f ξ) * hT + (tlNCbQ31c1 f ξ) * hT + (tlNCbQ31c2 f ξ) * hT + (tlNCbQ31c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP31c0, tlNCbP31c1, tlNCbP31c10, tlNCbP31c11,
      tlNCbP31c12, tlNCbP31c13, tlNCbP31c2, tlNCbP31c3, tlNCbP31c4, tlNCbP31c5,
      tlNCbP31c6, tlNCbP31c7, tlNCbP31c8, tlNCbP31c9, tlNCbQ31c0, tlNCbQ31c1,
      tlNCbQ31c2, tlNCbQ31c3, tlNSqP3c2, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlNCb_s30_tlNCb_s31 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) +
        ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) +
        (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        tlNCbP30c12 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP31c0 f ξ + tlNCbP31c1 f ξ) + (tlNCbP31c2 f ξ + tlNCbP31c3 f ξ)) +
        ((tlNCbP31c4 f ξ + tlNCbP31c5 f ξ) + (tlNCbP31c6 f ξ + tlNCbP31c7 f ξ))) +
        (((tlNCbP31c8 f ξ + tlNCbP31c9 f ξ) + (tlNCbP31c10 f ξ + tlNCbP31c11 f ξ)) +
        (tlNCbP31c12 f ξ + tlNCbP31c13 f ξ))) := by
  exact ⟨MazurTorsion.Kubert.tlNCb_s30, MazurTorsion.Kubert.tlNCb_s31⟩

#print axioms MazurTransfer.order27_certificate_tlNCb_s30_tlNCb_s31


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) +
        ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) +
        (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        tlNCbP30c12 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP31c0 f ξ + tlNCbP31c1 f ξ) + (tlNCbP31c2 f ξ + tlNCbP31c3 f ξ)) +
        ((tlNCbP31c4 f ξ + tlNCbP31c5 f ξ) + (tlNCbP31c6 f ξ + tlNCbP31c7 f ξ))) +
        (((tlNCbP31c8 f ξ + tlNCbP31c9 f ξ) + (tlNCbP31c10 f ξ + tlNCbP31c11 f ξ)) +
        (tlNCbP31c12 f ξ + tlNCbP31c13 f ξ)))  := by
  exact MazurTransfer.order27_certificate_tlNCb_s30_tlNCb_s31

#print axioms solution
