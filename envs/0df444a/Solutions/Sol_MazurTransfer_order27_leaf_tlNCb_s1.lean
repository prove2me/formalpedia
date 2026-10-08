-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:28:24.48066+00:00
-- url     : https://prove2.me/submissions/b5bbf1f6-9ed6-4fc5-8fc2-5269c7448b04

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP1c0 f ξ + tlNCbP1c1 f ξ) + (tlNCbP1c2 f ξ + tlNCbP1c3 f ξ)) + ((tlNCbP1c4 f
        ξ + tlNCbP1c5 f ξ) + (tlNCbP1c6 f ξ + tlNCbP1c7 f ξ))) + (((tlNCbP1c8 f ξ +
        tlNCbP1c9 f ξ) + (tlNCbP1c10 f ξ + tlNCbP1c11 f ξ)) + tlNCbP1c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ1c0 f ξ) * hT + (tlNCbQ1c1 f ξ) * hT + (tlNCbQ1c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP1c0, tlNCbP1c1, tlNCbP1c10, tlNCbP1c11,
      tlNCbP1c12, tlNCbP1c2, tlNCbP1c3, tlNCbP1c4, tlNCbP1c5, tlNCbP1c6, tlNCbP1c7,
      tlNCbP1c8, tlNCbP1c9, tlNCbQ1c0, tlNCbQ1c1, tlNCbQ1c2, tlNSqP0c1, tlT0, tlT1,
      tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP1c0 f ξ + tlNCbP1c1 f ξ) + (tlNCbP1c2 f ξ + tlNCbP1c3 f ξ)) + ((tlNCbP1c4 f
        ξ + tlNCbP1c5 f ξ) + (tlNCbP1c6 f ξ + tlNCbP1c7 f ξ))) + (((tlNCbP1c8 f ξ +
        tlNCbP1c9 f ξ) + (tlNCbP1c10 f ξ + tlNCbP1c11 f ξ)) + tlNCbP1c12 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s1

#print axioms solution
