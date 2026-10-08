-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:32:21.972013+00:00
-- url     : https://prove2.me/submissions/66ec6b63-ba97-429f-9f92-57716f1b10b8

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f
        ξ + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + ((tlNCbP0c8 f ξ +
        tlNCbP0c9 f ξ) + tlNCbP0c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ0c0 f ξ) * hT + (tlNCbQ0c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP0c0, tlNCbP0c1, tlNCbP0c10, tlNCbP0c2, tlNCbP0c3,
      tlNCbP0c4, tlNCbP0c5, tlNCbP0c6, tlNCbP0c7, tlNCbP0c8, tlNCbP0c9, tlNCbQ0c0,
      tlNCbQ0c1, tlNSqP0c0, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f
        ξ + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + ((tlNCbP0c8 f ξ +
        tlNCbP0c9 f ξ) + tlNCbP0c10 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s0

#print axioms solution
