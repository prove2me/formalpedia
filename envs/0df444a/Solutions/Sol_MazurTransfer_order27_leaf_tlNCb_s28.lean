-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s28
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:21.200985+00:00
-- url     : https://prove2.me/submissions/c493791c-be06-4a3f-846a-c382cc90496b

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s28 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP28c0 f ξ + tlNCbP28c1 f ξ) + (tlNCbP28c2 f ξ + tlNCbP28c3 f ξ)) +
        ((tlNCbP28c4 f ξ + tlNCbP28c5 f ξ) + (tlNCbP28c6 f ξ + tlNCbP28c7 f ξ))) +
        (((tlNCbP28c8 f ξ + tlNCbP28c9 f ξ) + (tlNCbP28c10 f ξ + tlNCbP28c11 f ξ)) +
        ((tlNCbP28c12 f ξ + tlNCbP28c13 f ξ) + (tlNCbP28c14 f ξ + tlNCbP28c15 f ξ)))) +
        ((tlNCbP28c16 f ξ + tlNCbP28c17 f ξ) + tlNCbP28c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ28c0 f ξ) * hT + (tlNCbQ28c1 f ξ) * hT + (tlNCbQ28c2 f ξ) * hT + (tlNCbQ28c3 f ξ) * hT
      + (tlNCbQ28c4 f ξ) * hT + (tlNCbQ28c5 f ξ) * hT + (tlNCbQ28c6 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP28c0, tlNCbP28c1, tlNCbP28c10, tlNCbP28c11,
      tlNCbP28c12, tlNCbP28c13, tlNCbP28c14, tlNCbP28c15, tlNCbP28c16, tlNCbP28c17,
      tlNCbP28c18, tlNCbP28c2, tlNCbP28c3, tlNCbP28c4, tlNCbP28c5, tlNCbP28c6,
      tlNCbP28c7, tlNCbP28c8, tlNCbP28c9, tlNCbQ28c0, tlNCbQ28c1, tlNCbQ28c2,
      tlNCbQ28c3, tlNCbQ28c4, tlNCbQ28c5, tlNCbQ28c6, tlNSqP2c10, tlNSqP2c11, tlT0,
      tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c10 f ξ + tlNSqP2c11 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP28c0 f ξ + tlNCbP28c1 f ξ) + (tlNCbP28c2 f ξ + tlNCbP28c3 f ξ)) +
        ((tlNCbP28c4 f ξ + tlNCbP28c5 f ξ) + (tlNCbP28c6 f ξ + tlNCbP28c7 f ξ))) +
        (((tlNCbP28c8 f ξ + tlNCbP28c9 f ξ) + (tlNCbP28c10 f ξ + tlNCbP28c11 f ξ)) +
        ((tlNCbP28c12 f ξ + tlNCbP28c13 f ξ) + (tlNCbP28c14 f ξ + tlNCbP28c15 f ξ)))) +
        ((tlNCbP28c16 f ξ + tlNCbP28c17 f ξ) + tlNCbP28c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s28

#print axioms solution
