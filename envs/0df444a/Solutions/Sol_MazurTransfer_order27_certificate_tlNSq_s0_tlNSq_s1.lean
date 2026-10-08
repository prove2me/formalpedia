-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlNSq_s0_tlNSq_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:21:39.254216+00:00
-- url     : https://prove2.me/submissions/61a65952-8188-4b37-a610-3f08f7549d92

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

lemma tlNSq_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f
        ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + tlNSqP0c8 f ξ := by
  linear_combination (norm := skip)
    (tlNSqQ0c0 f ξ) * hT + (tlNSqQ0c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP0c0, tlNSqP0c1, tlNSqP0c2, tlNSqP0c3, tlNSqP0c4,
      tlNSqP0c5, tlNSqP0c6, tlNSqP0c7, tlNSqP0c8, tlNSqQ0c0, tlNSqQ0c1, tlT0, tlT1,
      tlT2, tlT3]
  ring1

lemma tlNSq_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP1c0 f ξ + tlNSqP1c1 f ξ) + (tlNSqP1c2 f ξ + tlNSqP1c3 f ξ)) + ((tlNSqP1c4 f
        ξ + tlNSqP1c5 f ξ) + (tlNSqP1c6 f ξ + tlNSqP1c7 f ξ))) + (tlNSqP1c8 f ξ +
        tlNSqP1c9 f ξ) := by
  linear_combination (norm := skip)
    (tlNSqQ1c0 f ξ) * hT + (tlNSqQ1c1 f ξ) * hT + (tlNSqQ1c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP1c0, tlNSqP1c1, tlNSqP1c2, tlNSqP1c3, tlNSqP1c4,
      tlNSqP1c5, tlNSqP1c6, tlNSqP1c7, tlNSqP1c8, tlNSqP1c9, tlNSqQ1c0, tlNSqQ1c1,
      tlNSqQ1c2, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_tlNSq_s0_tlNSq_s1 :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f
        ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + tlNSqP0c8 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP1c0 f ξ + tlNSqP1c1 f ξ) + (tlNSqP1c2 f ξ + tlNSqP1c3 f ξ)) + ((tlNSqP1c4 f
        ξ + tlNSqP1c5 f ξ) + (tlNSqP1c6 f ξ + tlNSqP1c7 f ξ))) + (tlNSqP1c8 f ξ +
        tlNSqP1c9 f ξ)) := by
  exact ⟨MazurTorsion.Kubert.tlNSq_s0, MazurTorsion.Kubert.tlNSq_s1⟩

#print axioms MazurTransfer.order27_certificate_tlNSq_s0_tlNSq_s1


theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f
        ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + tlNSqP0c8 f ξ)
  ∧ (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP1c0 f ξ + tlNSqP1c1 f ξ) + (tlNSqP1c2 f ξ + tlNSqP1c3 f ξ)) + ((tlNSqP1c4 f
        ξ + tlNSqP1c5 f ξ) + (tlNSqP1c6 f ξ + tlNSqP1c7 f ξ))) + (tlNSqP1c8 f ξ +
        tlNSqP1c9 f ξ))  := by
  exact MazurTransfer.order27_certificate_tlNSq_s0_tlNSq_s1

#print axioms solution
