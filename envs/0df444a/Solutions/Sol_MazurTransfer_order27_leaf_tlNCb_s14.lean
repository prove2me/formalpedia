-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s14
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:33:55.890269+00:00
-- url     : https://prove2.me/submissions/183167b4-6490-4512-9152-21f934db61fa

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s14 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP14c0 f ξ + tlNCbP14c1 f ξ) + (tlNCbP14c2 f ξ + tlNCbP14c3 f ξ)) +
        ((tlNCbP14c4 f ξ + tlNCbP14c5 f ξ) + (tlNCbP14c6 f ξ + tlNCbP14c7 f ξ))) +
        (((tlNCbP14c8 f ξ + tlNCbP14c9 f ξ) + (tlNCbP14c10 f ξ + tlNCbP14c11 f ξ)) +
        ((tlNCbP14c12 f ξ + tlNCbP14c13 f ξ) + (tlNCbP14c14 f ξ + tlNCbP14c15 f ξ)))) +
        (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ14c0 f ξ) * hT + (tlNCbQ14c1 f ξ) * hT + (tlNCbQ14c2 f ξ) * hT + (tlNCbQ14c3 f ξ) * hT
      + (tlNCbQ14c4 f ξ) * hT + (tlNCbQ14c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP14c0, tlNCbP14c1, tlNCbP14c10, tlNCbP14c11,
      tlNCbP14c12, tlNCbP14c13, tlNCbP14c14, tlNCbP14c15, tlNCbP14c16, tlNCbP14c17,
      tlNCbP14c2, tlNCbP14c3, tlNCbP14c4, tlNCbP14c5, tlNCbP14c6, tlNCbP14c7,
      tlNCbP14c8, tlNCbP14c9, tlNCbQ14c0, tlNCbQ14c1, tlNCbQ14c2, tlNCbQ14c3,
      tlNCbQ14c4, tlNCbQ14c5, tlNSqP1c6, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP14c0 f ξ + tlNCbP14c1 f ξ) + (tlNCbP14c2 f ξ + tlNCbP14c3 f ξ)) +
        ((tlNCbP14c4 f ξ + tlNCbP14c5 f ξ) + (tlNCbP14c6 f ξ + tlNCbP14c7 f ξ))) +
        (((tlNCbP14c8 f ξ + tlNCbP14c9 f ξ) + (tlNCbP14c10 f ξ + tlNCbP14c11 f ξ)) +
        ((tlNCbP14c12 f ξ + tlNCbP14c13 f ξ) + (tlNCbP14c14 f ξ + tlNCbP14c15 f ξ)))) +
        (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s14

#print axioms solution
