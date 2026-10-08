-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s20
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:34:37.699172+00:00
-- url     : https://prove2.me/submissions/becbc135-3bf4-4884-8025-343a20b54165

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s20 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP20c0 f ξ + tlNCbP20c1 f ξ) + (tlNCbP20c2 f ξ + tlNCbP20c3 f ξ)) +
        ((tlNCbP20c4 f ξ + tlNCbP20c5 f ξ) + (tlNCbP20c6 f ξ + tlNCbP20c7 f ξ))) +
        (((tlNCbP20c8 f ξ + tlNCbP20c9 f ξ) + (tlNCbP20c10 f ξ + tlNCbP20c11 f ξ)) +
        (tlNCbP20c12 f ξ + tlNCbP20c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ20c0 f ξ) * hT + (tlNCbQ20c1 f ξ) * hT + (tlNCbQ20c2 f ξ) * hT + (tlNCbQ20c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP20c0, tlNCbP20c1, tlNCbP20c10, tlNCbP20c11,
      tlNCbP20c12, tlNCbP20c13, tlNCbP20c2, tlNCbP20c3, tlNCbP20c4, tlNCbP20c5,
      tlNCbP20c6, tlNCbP20c7, tlNCbP20c8, tlNCbP20c9, tlNCbQ20c0, tlNCbQ20c1,
      tlNCbQ20c2, tlNCbQ20c3, tlNSqP2c2, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP20c0 f ξ + tlNCbP20c1 f ξ) + (tlNCbP20c2 f ξ + tlNCbP20c3 f ξ)) +
        ((tlNCbP20c4 f ξ + tlNCbP20c5 f ξ) + (tlNCbP20c6 f ξ + tlNCbP20c7 f ξ))) +
        (((tlNCbP20c8 f ξ + tlNCbP20c9 f ξ) + (tlNCbP20c10 f ξ + tlNCbP20c11 f ξ)) +
        (tlNCbP20c12 f ξ + tlNCbP20c13 f ξ))) := by
  exact MazurTorsion.Kubert.tlNCb_s20

#print axioms solution
