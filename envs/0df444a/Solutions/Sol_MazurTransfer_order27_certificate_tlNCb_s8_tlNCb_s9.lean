-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s8_tlNCb_s9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:21:46.42398+00:00
-- url     : https://prove2.me/submissions/8ff47ae9-4c64-4222-9755-30a5d0d1d5db

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

lemma tlNCb_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP8c0 f ξ + tlNCbP8c1 f ξ) + (tlNCbP8c2 f ξ + tlNCbP8c3 f ξ)) + ((tlNCbP8c4 f
        ξ + tlNCbP8c5 f ξ) + (tlNCbP8c6 f ξ + tlNCbP8c7 f ξ))) + ((tlNCbP8c8 f ξ +
        tlNCbP8c9 f ξ) + tlNCbP8c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ8c0 f ξ) * hT + (tlNCbQ8c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP8c0, tlNCbP8c1, tlNCbP8c10, tlNCbP8c2, tlNCbP8c3,
      tlNCbP8c4, tlNCbP8c5, tlNCbP8c6, tlNCbP8c7, tlNCbP8c8, tlNCbP8c9, tlNCbQ8c0,
      tlNCbQ8c1, tlNSqP1c0, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP9c0 f ξ + tlNCbP9c1 f ξ) + (tlNCbP9c2 f ξ + tlNCbP9c3 f ξ)) + ((tlNCbP9c4 f
        ξ + tlNCbP9c5 f ξ) + (tlNCbP9c6 f ξ + tlNCbP9c7 f ξ))) + (((tlNCbP9c8 f ξ +
        tlNCbP9c9 f ξ) + (tlNCbP9c10 f ξ + tlNCbP9c11 f ξ)) + tlNCbP9c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ9c0 f ξ) * hT + (tlNCbQ9c1 f ξ) * hT + (tlNCbQ9c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP9c0, tlNCbP9c1, tlNCbP9c10, tlNCbP9c11,
      tlNCbP9c12, tlNCbP9c2, tlNCbP9c3, tlNCbP9c4, tlNCbP9c5, tlNCbP9c6, tlNCbP9c7,
      tlNCbP9c8, tlNCbP9c9, tlNCbQ9c0, tlNCbQ9c1, tlNCbQ9c2, tlNSqP1c1, tlT0, tlT1,
      tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlNCb_s8_tlNCb_s9 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP8c0 f ξ + tlNCbP8c1 f ξ) + (tlNCbP8c2 f ξ + tlNCbP8c3 f ξ)) + ((tlNCbP8c4 f
        ξ + tlNCbP8c5 f ξ) + (tlNCbP8c6 f ξ + tlNCbP8c7 f ξ))) + ((tlNCbP8c8 f ξ +
        tlNCbP8c9 f ξ) + tlNCbP8c10 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP9c0 f ξ + tlNCbP9c1 f ξ) + (tlNCbP9c2 f ξ + tlNCbP9c3 f ξ)) + ((tlNCbP9c4 f
        ξ + tlNCbP9c5 f ξ) + (tlNCbP9c6 f ξ + tlNCbP9c7 f ξ))) + (((tlNCbP9c8 f ξ +
        tlNCbP9c9 f ξ) + (tlNCbP9c10 f ξ + tlNCbP9c11 f ξ)) + tlNCbP9c12 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlNCb_s8, MazurTorsion.Kubert.tlNCb_s9⟩

#print axioms MazurTransfer.order27_certificate_tlNCb_s8_tlNCb_s9


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP8c0 f ξ + tlNCbP8c1 f ξ) + (tlNCbP8c2 f ξ + tlNCbP8c3 f ξ)) + ((tlNCbP8c4 f
        ξ + tlNCbP8c5 f ξ) + (tlNCbP8c6 f ξ + tlNCbP8c7 f ξ))) + ((tlNCbP8c8 f ξ +
        tlNCbP8c9 f ξ) + tlNCbP8c10 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP9c0 f ξ + tlNCbP9c1 f ξ) + (tlNCbP9c2 f ξ + tlNCbP9c3 f ξ)) + ((tlNCbP9c4 f
        ξ + tlNCbP9c5 f ξ) + (tlNCbP9c6 f ξ + tlNCbP9c7 f ξ))) + (((tlNCbP9c8 f ξ +
        tlNCbP9c9 f ξ) + (tlNCbP9c10 f ξ + tlNCbP9c11 f ξ)) + tlNCbP9c12 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlNCb_s8_tlNCb_s9

#print axioms solution
