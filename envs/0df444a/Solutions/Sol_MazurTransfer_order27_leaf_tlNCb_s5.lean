-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:29:03.407038+00:00
-- url     : https://prove2.me/submissions/d918037d-ff4a-4115-991e-1001d9e12663

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4
        f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ))) + (((tlNCbP5c8 f ξ +
        tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ +
        tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ)))) + (tlNCbP5c16 f ξ +
        tlNCbP5c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ5c0 f ξ) * hT + (tlNCbQ5c1 f ξ) * hT + (tlNCbQ5c2 f ξ) * hT + (tlNCbQ5c3 f ξ) * hT +
      (tlNCbQ5c4 f ξ) * hT + (tlNCbQ5c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP5c0, tlNCbP5c1, tlNCbP5c10, tlNCbP5c11,
      tlNCbP5c12, tlNCbP5c13, tlNCbP5c14, tlNCbP5c15, tlNCbP5c16, tlNCbP5c17,
      tlNCbP5c2, tlNCbP5c3, tlNCbP5c4, tlNCbP5c5, tlNCbP5c6, tlNCbP5c7, tlNCbP5c8,
      tlNCbP5c9, tlNCbQ5c0, tlNCbQ5c1, tlNCbQ5c2, tlNCbQ5c3, tlNCbQ5c4, tlNCbQ5c5,
      tlNSqP0c5, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4
        f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ))) + (((tlNCbP5c8 f ξ +
        tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ +
        tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ)))) + (tlNCbP5c16 f ξ +
        tlNCbP5c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s5

#print axioms solution
