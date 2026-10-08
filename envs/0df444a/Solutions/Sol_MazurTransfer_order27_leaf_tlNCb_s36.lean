-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s36
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:30.565704+00:00
-- url     : https://prove2.me/submissions/e0711aa8-5cc1-4760-9b20-979ff4647409

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s36 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) +
        (((tlNCbP36c8 f ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) +
        ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) +
        ((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) + tlNCbP36c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ36c0 f ξ) * hT + (tlNCbQ36c1 f ξ) * hT + (tlNCbQ36c2 f ξ) * hT + (tlNCbQ36c3 f ξ) * hT
      + (tlNCbQ36c4 f ξ) * hT + (tlNCbQ36c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP36c0, tlNCbP36c1, tlNCbP36c10, tlNCbP36c11,
      tlNCbP36c12, tlNCbP36c13, tlNCbP36c14, tlNCbP36c15, tlNCbP36c16, tlNCbP36c17,
      tlNCbP36c18, tlNCbP36c2, tlNCbP36c3, tlNCbP36c4, tlNCbP36c5, tlNCbP36c6,
      tlNCbP36c7, tlNCbP36c8, tlNCbP36c9, tlNCbQ36c0, tlNCbQ36c1, tlNCbQ36c2,
      tlNCbQ36c3, tlNCbQ36c4, tlNCbQ36c5, tlNSqP3c7, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) +
        (((tlNCbP36c8 f ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) +
        ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) +
        ((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) + tlNCbP36c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s36

#print axioms solution
