-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s17
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:41.172978+00:00
-- url     : https://prove2.me/submissions/e636cd1d-9d5d-4384-badd-c22e3ace4e84

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s17 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP17c0 f ξ + tlNCbP17c1 f ξ) + (tlNCbP17c2 f ξ + tlNCbP17c3 f ξ)) +
        ((tlNCbP17c4 f ξ + tlNCbP17c5 f ξ) + (tlNCbP17c6 f ξ + tlNCbP17c7 f ξ))) +
        (((tlNCbP17c8 f ξ + tlNCbP17c9 f ξ) + (tlNCbP17c10 f ξ + tlNCbP17c11 f ξ)) +
        ((tlNCbP17c12 f ξ + tlNCbP17c13 f ξ) + (tlNCbP17c14 f ξ + tlNCbP17c15 f ξ)))) +
        ((tlNCbP17c16 f ξ + tlNCbP17c17 f ξ) + tlNCbP17c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ17c0 f ξ) * hT + (tlNCbQ17c1 f ξ) * hT + (tlNCbQ17c2 f ξ) * hT + (tlNCbQ17c3 f ξ) * hT
      + (tlNCbQ17c4 f ξ) * hT + (tlNCbQ17c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP17c0, tlNCbP17c1, tlNCbP17c10, tlNCbP17c11,
      tlNCbP17c12, tlNCbP17c13, tlNCbP17c14, tlNCbP17c15, tlNCbP17c16, tlNCbP17c17,
      tlNCbP17c18, tlNCbP17c2, tlNCbP17c3, tlNCbP17c4, tlNCbP17c5, tlNCbP17c6,
      tlNCbP17c7, tlNCbP17c8, tlNCbP17c9, tlNCbQ17c0, tlNCbQ17c1, tlNCbQ17c2,
      tlNCbQ17c3, tlNCbQ17c4, tlNCbQ17c5, tlNSqP1c9, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP17c0 f ξ + tlNCbP17c1 f ξ) + (tlNCbP17c2 f ξ + tlNCbP17c3 f ξ)) +
        ((tlNCbP17c4 f ξ + tlNCbP17c5 f ξ) + (tlNCbP17c6 f ξ + tlNCbP17c7 f ξ))) +
        (((tlNCbP17c8 f ξ + tlNCbP17c9 f ξ) + (tlNCbP17c10 f ξ + tlNCbP17c11 f ξ)) +
        ((tlNCbP17c12 f ξ + tlNCbP17c13 f ξ) + (tlNCbP17c14 f ξ + tlNCbP17c15 f ξ)))) +
        ((tlNCbP17c16 f ξ + tlNCbP17c17 f ξ) + tlNCbP17c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s17

#print axioms solution
