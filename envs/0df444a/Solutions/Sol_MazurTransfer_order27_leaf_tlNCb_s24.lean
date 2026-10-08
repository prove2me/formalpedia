-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s24
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:18.000148+00:00
-- url     : https://prove2.me/submissions/c5b460db-df80-4a21-b720-64649d6147e1

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s24 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP24c0 f ξ + tlNCbP24c1 f ξ) + (tlNCbP24c2 f ξ + tlNCbP24c3 f ξ)) +
        ((tlNCbP24c4 f ξ + tlNCbP24c5 f ξ) + (tlNCbP24c6 f ξ + tlNCbP24c7 f ξ))) +
        (((tlNCbP24c8 f ξ + tlNCbP24c9 f ξ) + (tlNCbP24c10 f ξ + tlNCbP24c11 f ξ)) +
        ((tlNCbP24c12 f ξ + tlNCbP24c13 f ξ) + (tlNCbP24c14 f ξ + tlNCbP24c15 f ξ)))) +
        (tlNCbP24c16 f ξ + tlNCbP24c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ24c0 f ξ) * hT + (tlNCbQ24c1 f ξ) * hT + (tlNCbQ24c2 f ξ) * hT + (tlNCbQ24c3 f ξ) * hT
      + (tlNCbQ24c4 f ξ) * hT + (tlNCbQ24c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP24c0, tlNCbP24c1, tlNCbP24c10, tlNCbP24c11,
      tlNCbP24c12, tlNCbP24c13, tlNCbP24c14, tlNCbP24c15, tlNCbP24c16, tlNCbP24c17,
      tlNCbP24c2, tlNCbP24c3, tlNCbP24c4, tlNCbP24c5, tlNCbP24c6, tlNCbP24c7,
      tlNCbP24c8, tlNCbP24c9, tlNCbQ24c0, tlNCbQ24c1, tlNCbQ24c2, tlNCbQ24c3,
      tlNCbQ24c4, tlNCbQ24c5, tlNSqP2c6, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP24c0 f ξ + tlNCbP24c1 f ξ) + (tlNCbP24c2 f ξ + tlNCbP24c3 f ξ)) +
        ((tlNCbP24c4 f ξ + tlNCbP24c5 f ξ) + (tlNCbP24c6 f ξ + tlNCbP24c7 f ξ))) +
        (((tlNCbP24c8 f ξ + tlNCbP24c9 f ξ) + (tlNCbP24c10 f ξ + tlNCbP24c11 f ξ)) +
        ((tlNCbP24c12 f ξ + tlNCbP24c13 f ξ) + (tlNCbP24c14 f ξ + tlNCbP24c15 f ξ)))) +
        (tlNCbP24c16 f ξ + tlNCbP24c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s24

#print axioms solution
