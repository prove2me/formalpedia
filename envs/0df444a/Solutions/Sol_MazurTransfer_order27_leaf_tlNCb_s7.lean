-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:36:41.691782+00:00
-- url     : https://prove2.me/submissions/af774488-ca84-48fa-9711-bba047ce7549

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c7 f ξ + tlNSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)) + ((tlNCbP7c4
        f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP7c8 f ξ +
        tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ)) + ((tlNCbP7c12 f ξ +
        tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)))) + ((tlNCbP7c16 f ξ +
        tlNCbP7c17 f ξ) + tlNCbP7c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ7c0 f ξ) * hT + (tlNCbQ7c1 f ξ) * hT + (tlNCbQ7c2 f ξ) * hT + (tlNCbQ7c3 f ξ) * hT +
      (tlNCbQ7c4 f ξ) * hT + (tlNCbQ7c5 f ξ) * hT + (tlNCbQ7c6 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP7c0, tlNCbP7c1, tlNCbP7c10, tlNCbP7c11,
      tlNCbP7c12, tlNCbP7c13, tlNCbP7c14, tlNCbP7c15, tlNCbP7c16, tlNCbP7c17,
      tlNCbP7c18, tlNCbP7c2, tlNCbP7c3, tlNCbP7c4, tlNCbP7c5, tlNCbP7c6, tlNCbP7c7,
      tlNCbP7c8, tlNCbP7c9, tlNCbQ7c0, tlNCbQ7c1, tlNCbQ7c2, tlNCbQ7c3, tlNCbQ7c4,
      tlNCbQ7c5, tlNCbQ7c6, tlNSqP0c7, tlNSqP0c8, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c7 f ξ + tlNSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)) + ((tlNCbP7c4
        f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP7c8 f ξ +
        tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ)) + ((tlNCbP7c12 f ξ +
        tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)))) + ((tlNCbP7c16 f ξ +
        tlNCbP7c17 f ξ) + tlNCbP7c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s7

#print axioms solution
