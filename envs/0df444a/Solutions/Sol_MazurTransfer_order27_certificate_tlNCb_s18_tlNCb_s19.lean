-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNCb_s18_tlNCb_s19
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:22:41.84588+00:00
-- url     : https://prove2.me/submissions/54dd11d7-dba1-4be1-8c05-9bb3ee70c35e

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

lemma tlNCb_s18 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP18c0 f ξ + tlNCbP18c1 f ξ) + (tlNCbP18c2 f ξ + tlNCbP18c3 f ξ)) +
        ((tlNCbP18c4 f ξ + tlNCbP18c5 f ξ) + (tlNCbP18c6 f ξ + tlNCbP18c7 f ξ))) +
        ((tlNCbP18c8 f ξ + tlNCbP18c9 f ξ) + tlNCbP18c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ18c0 f ξ) * hT + (tlNCbQ18c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP18c0, tlNCbP18c1, tlNCbP18c10, tlNCbP18c2,
      tlNCbP18c3, tlNCbP18c4, tlNCbP18c5, tlNCbP18c6, tlNCbP18c7, tlNCbP18c8,
      tlNCbP18c9, tlNCbQ18c0, tlNCbQ18c1, tlNSqP2c0, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s19 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)) +
        ((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ))) +
        (((tlNCbP19c8 f ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ)) +
        tlNCbP19c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ19c0 f ξ) * hT + (tlNCbQ19c1 f ξ) * hT + (tlNCbQ19c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP19c0, tlNCbP19c1, tlNCbP19c10, tlNCbP19c11,
      tlNCbP19c12, tlNCbP19c2, tlNCbP19c3, tlNCbP19c4, tlNCbP19c5, tlNCbP19c6,
      tlNCbP19c7, tlNCbP19c8, tlNCbP19c9, tlNCbQ19c0, tlNCbQ19c1, tlNCbQ19c2,
      tlNSqP2c1, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlNCb_s18_tlNCb_s19 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP18c0 f ξ + tlNCbP18c1 f ξ) + (tlNCbP18c2 f ξ + tlNCbP18c3 f ξ)) +
        ((tlNCbP18c4 f ξ + tlNCbP18c5 f ξ) + (tlNCbP18c6 f ξ + tlNCbP18c7 f ξ))) +
        ((tlNCbP18c8 f ξ + tlNCbP18c9 f ξ) + tlNCbP18c10 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)) +
        ((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ))) +
        (((tlNCbP19c8 f ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ)) +
        tlNCbP19c12 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlNCb_s18, MazurTorsion.Kubert.tlNCb_s19⟩

#print axioms MazurTransfer.order27_certificate_tlNCb_s18_tlNCb_s19


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP18c0 f ξ + tlNCbP18c1 f ξ) + (tlNCbP18c2 f ξ + tlNCbP18c3 f ξ)) +
        ((tlNCbP18c4 f ξ + tlNCbP18c5 f ξ) + (tlNCbP18c6 f ξ + tlNCbP18c7 f ξ))) +
        ((tlNCbP18c8 f ξ + tlNCbP18c9 f ξ) + tlNCbP18c10 f ξ))
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)) +
        ((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ))) +
        (((tlNCbP19c8 f ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ)) +
        tlNCbP19c12 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlNCb_s18_tlNCb_s19

#print axioms solution
