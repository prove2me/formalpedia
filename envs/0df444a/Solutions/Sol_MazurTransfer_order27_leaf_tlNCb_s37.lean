-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s37
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:40:56.310113+00:00
-- url     : https://prove2.me/submissions/38a38a51-ad31-47b8-9333-ec1c42e6af39

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s37 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP37c0 f + tlNCbP37c1 f ξ) + (tlNCbP37c2 f ξ + tlNCbP37c3 f ξ)) +
        ((tlNCbP37c4 f ξ + tlNCbP37c5 f ξ) + (tlNCbP37c6 f ξ + tlNCbP37c7 f ξ))) +
        (((tlNCbP37c8 f ξ + tlNCbP37c9 f ξ) + (tlNCbP37c10 f ξ + tlNCbP37c11 f ξ)) +
        ((tlNCbP37c12 f ξ + tlNCbP37c13 f ξ) + (tlNCbP37c14 f ξ + tlNCbP37c15 f ξ)))) +
        ((tlNCbP37c16 f ξ + tlNCbP37c17 f ξ) + tlNCbP37c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ37c0 f ξ) * hT + (tlNCbQ37c1 f ξ) * hT + (tlNCbQ37c2 f ξ) * hT + (tlNCbQ37c3 f ξ) * hT
      + (tlNCbQ37c4 f ξ) * hT + (tlNCbQ37c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP37c0, tlNCbP37c1, tlNCbP37c10, tlNCbP37c11,
      tlNCbP37c12, tlNCbP37c13, tlNCbP37c14, tlNCbP37c15, tlNCbP37c16, tlNCbP37c17,
      tlNCbP37c18, tlNCbP37c2, tlNCbP37c3, tlNCbP37c4, tlNCbP37c5, tlNCbP37c6,
      tlNCbP37c7, tlNCbP37c8, tlNCbP37c9, tlNCbQ37c0, tlNCbQ37c1, tlNCbQ37c2,
      tlNCbQ37c3, tlNCbQ37c4, tlNCbQ37c5, tlNSqP3c8, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP37c0 f + tlNCbP37c1 f ξ) + (tlNCbP37c2 f ξ + tlNCbP37c3 f ξ)) +
        ((tlNCbP37c4 f ξ + tlNCbP37c5 f ξ) + (tlNCbP37c6 f ξ + tlNCbP37c7 f ξ))) +
        (((tlNCbP37c8 f ξ + tlNCbP37c9 f ξ) + (tlNCbP37c10 f ξ + tlNCbP37c11 f ξ)) +
        ((tlNCbP37c12 f ξ + tlNCbP37c13 f ξ) + (tlNCbP37c14 f ξ + tlNCbP37c15 f ξ)))) +
        ((tlNCbP37c16 f ξ + tlNCbP37c17 f ξ) + tlNCbP37c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s37

#print axioms solution
