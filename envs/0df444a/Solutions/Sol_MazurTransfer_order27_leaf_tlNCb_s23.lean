-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s23
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:36:37.527816+00:00
-- url     : https://prove2.me/submissions/ff7fbfd8-f867-49a5-a279-d308bc5a95e1

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s23 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP23c0 f ξ + tlNCbP23c1 f ξ) + (tlNCbP23c2 f ξ + tlNCbP23c3 f ξ)) +
        ((tlNCbP23c4 f ξ + tlNCbP23c5 f ξ) + (tlNCbP23c6 f ξ + tlNCbP23c7 f ξ))) +
        (((tlNCbP23c8 f ξ + tlNCbP23c9 f ξ) + (tlNCbP23c10 f ξ + tlNCbP23c11 f ξ)) +
        ((tlNCbP23c12 f ξ + tlNCbP23c13 f ξ) + (tlNCbP23c14 f ξ + tlNCbP23c15 f ξ)))) +
        tlNCbP23c16 f ξ := by
  linear_combination (norm := skip)
    (tlNCbQ23c0 f ξ) * hT + (tlNCbQ23c1 f ξ) * hT + (tlNCbQ23c2 f ξ) * hT + (tlNCbQ23c3 f ξ) * hT
      + (tlNCbQ23c4 f ξ) * hT + (tlNCbQ23c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP23c0, tlNCbP23c1, tlNCbP23c10, tlNCbP23c11,
      tlNCbP23c12, tlNCbP23c13, tlNCbP23c14, tlNCbP23c15, tlNCbP23c16, tlNCbP23c2,
      tlNCbP23c3, tlNCbP23c4, tlNCbP23c5, tlNCbP23c6, tlNCbP23c7, tlNCbP23c8,
      tlNCbP23c9, tlNCbQ23c0, tlNCbQ23c1, tlNCbQ23c2, tlNCbQ23c3, tlNCbQ23c4,
      tlNCbQ23c5, tlNSqP2c5, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP23c0 f ξ + tlNCbP23c1 f ξ) + (tlNCbP23c2 f ξ + tlNCbP23c3 f ξ)) +
        ((tlNCbP23c4 f ξ + tlNCbP23c5 f ξ) + (tlNCbP23c6 f ξ + tlNCbP23c7 f ξ))) +
        (((tlNCbP23c8 f ξ + tlNCbP23c9 f ξ) + (tlNCbP23c10 f ξ + tlNCbP23c11 f ξ)) +
        ((tlNCbP23c12 f ξ + tlNCbP23c13 f ξ) + (tlNCbP23c14 f ξ + tlNCbP23c15 f ξ)))) +
        tlNCbP23c16 f ξ) := by
  exact MazurTorsion.Kubert.tlNCb_s23

#print axioms solution
