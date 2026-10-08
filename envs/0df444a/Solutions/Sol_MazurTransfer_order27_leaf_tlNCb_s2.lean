-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:28:25.666358+00:00
-- url     : https://prove2.me/submissions/a1151696-d84a-4016-b99a-769e6a1bf74e

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP2c0 f ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f
        ξ + tlNCbP2c5 f ξ) + (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))) + (((tlNCbP2c8 f ξ +
        tlNCbP2c9 f ξ) + (tlNCbP2c10 f ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ +
        tlNCbP2c13 f ξ) + tlNCbP2c14 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ2c0 f ξ) * hT + (tlNCbQ2c1 f ξ) * hT + (tlNCbQ2c2 f ξ) * hT + (tlNCbQ2c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP2c0, tlNCbP2c1, tlNCbP2c10, tlNCbP2c11,
      tlNCbP2c12, tlNCbP2c13, tlNCbP2c14, tlNCbP2c2, tlNCbP2c3, tlNCbP2c4,
      tlNCbP2c5, tlNCbP2c6, tlNCbP2c7, tlNCbP2c8, tlNCbP2c9, tlNCbQ2c0, tlNCbQ2c1,
      tlNCbQ2c2, tlNCbQ2c3, tlNSqP0c2, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP2c0 f ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f
        ξ + tlNCbP2c5 f ξ) + (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))) + (((tlNCbP2c8 f ξ +
        tlNCbP2c9 f ξ) + (tlNCbP2c10 f ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ +
        tlNCbP2c13 f ξ) + tlNCbP2c14 f ξ))) := by
  exact MazurTorsion.Kubert.tlNCb_s2

#print axioms solution
