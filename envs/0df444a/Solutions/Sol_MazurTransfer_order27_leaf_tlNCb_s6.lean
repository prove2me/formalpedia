-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:36:40.503631+00:00
-- url     : https://prove2.me/submissions/312f9a44-9011-4c7b-a667-eba6bf40117f

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP6c0 f ξ + tlNCbP6c1 f ξ) + (tlNCbP6c2 f ξ + tlNCbP6c3 f ξ)) + ((tlNCbP6c4
        f ξ + tlNCbP6c5 f ξ) + (tlNCbP6c6 f ξ + tlNCbP6c7 f ξ))) + (((tlNCbP6c8 f ξ +
        tlNCbP6c9 f ξ) + (tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)) + ((tlNCbP6c12 f ξ +
        tlNCbP6c13 f ξ) + (tlNCbP6c14 f ξ + tlNCbP6c15 f ξ)))) + (tlNCbP6c16 f ξ +
        tlNCbP6c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ6c0 f ξ) * hT + (tlNCbQ6c1 f ξ) * hT + (tlNCbQ6c2 f ξ) * hT + (tlNCbQ6c3 f ξ) * hT +
      (tlNCbQ6c4 f ξ) * hT + (tlNCbQ6c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP6c0, tlNCbP6c1, tlNCbP6c10, tlNCbP6c11,
      tlNCbP6c12, tlNCbP6c13, tlNCbP6c14, tlNCbP6c15, tlNCbP6c16, tlNCbP6c17,
      tlNCbP6c2, tlNCbP6c3, tlNCbP6c4, tlNCbP6c5, tlNCbP6c6, tlNCbP6c7, tlNCbP6c8,
      tlNCbP6c9, tlNCbQ6c0, tlNCbQ6c1, tlNCbQ6c2, tlNCbQ6c3, tlNCbQ6c4, tlNCbQ6c5,
      tlNSqP0c6, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP6c0 f ξ + tlNCbP6c1 f ξ) + (tlNCbP6c2 f ξ + tlNCbP6c3 f ξ)) + ((tlNCbP6c4
        f ξ + tlNCbP6c5 f ξ) + (tlNCbP6c6 f ξ + tlNCbP6c7 f ξ))) + (((tlNCbP6c8 f ξ +
        tlNCbP6c9 f ξ) + (tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)) + ((tlNCbP6c12 f ξ +
        tlNCbP6c13 f ξ) + (tlNCbP6c14 f ξ + tlNCbP6c15 f ξ)))) + (tlNCbP6c16 f ξ +
        tlNCbP6c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s6

#print axioms solution
