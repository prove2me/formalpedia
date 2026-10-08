-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s35
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:38:47.963076+00:00
-- url     : https://prove2.me/submissions/b622deb9-f47c-42cc-8706-e21895f26097

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s35 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP35c0 f ξ + tlNCbP35c1 f ξ) + (tlNCbP35c2 f ξ + tlNCbP35c3 f ξ)) +
        ((tlNCbP35c4 f ξ + tlNCbP35c5 f ξ) + (tlNCbP35c6 f ξ + tlNCbP35c7 f ξ))) +
        (((tlNCbP35c8 f ξ + tlNCbP35c9 f ξ) + (tlNCbP35c10 f ξ + tlNCbP35c11 f ξ)) +
        ((tlNCbP35c12 f ξ + tlNCbP35c13 f ξ) + (tlNCbP35c14 f ξ + tlNCbP35c15 f ξ)))) +
        (tlNCbP35c16 f ξ + tlNCbP35c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ35c0 f ξ) * hT + (tlNCbQ35c1 f ξ) * hT + (tlNCbQ35c2 f ξ) * hT + (tlNCbQ35c3 f ξ) * hT
      + (tlNCbQ35c4 f ξ) * hT + (tlNCbQ35c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP35c0, tlNCbP35c1, tlNCbP35c10, tlNCbP35c11,
      tlNCbP35c12, tlNCbP35c13, tlNCbP35c14, tlNCbP35c15, tlNCbP35c16, tlNCbP35c17,
      tlNCbP35c2, tlNCbP35c3, tlNCbP35c4, tlNCbP35c5, tlNCbP35c6, tlNCbP35c7,
      tlNCbP35c8, tlNCbP35c9, tlNCbQ35c0, tlNCbQ35c1, tlNCbQ35c2, tlNCbQ35c3,
      tlNCbQ35c4, tlNCbQ35c5, tlNSqP3c6, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP35c0 f ξ + tlNCbP35c1 f ξ) + (tlNCbP35c2 f ξ + tlNCbP35c3 f ξ)) +
        ((tlNCbP35c4 f ξ + tlNCbP35c5 f ξ) + (tlNCbP35c6 f ξ + tlNCbP35c7 f ξ))) +
        (((tlNCbP35c8 f ξ + tlNCbP35c9 f ξ) + (tlNCbP35c10 f ξ + tlNCbP35c11 f ξ)) +
        ((tlNCbP35c12 f ξ + tlNCbP35c13 f ξ) + (tlNCbP35c14 f ξ + tlNCbP35c15 f ξ)))) +
        (tlNCbP35c16 f ξ + tlNCbP35c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s35

#print axioms solution
