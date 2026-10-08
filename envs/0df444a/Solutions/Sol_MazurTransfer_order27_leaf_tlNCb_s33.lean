-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s33
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:25.069336+00:00
-- url     : https://prove2.me/submissions/f59d0d1b-8237-46d5-8525-3f0851aa19c1

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s33 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP33c0 f ξ + tlNCbP33c1 f ξ) + (tlNCbP33c2 f ξ + tlNCbP33c3 f ξ)) +
        ((tlNCbP33c4 f ξ + tlNCbP33c5 f ξ) + (tlNCbP33c6 f ξ + tlNCbP33c7 f ξ))) +
        (((tlNCbP33c8 f ξ + tlNCbP33c9 f ξ) + (tlNCbP33c10 f ξ + tlNCbP33c11 f ξ)) +
        ((tlNCbP33c12 f ξ + tlNCbP33c13 f ξ) + (tlNCbP33c14 f ξ + tlNCbP33c15 f ξ)))) +
        tlNCbP33c16 f ξ := by
  linear_combination (norm := skip)
    (tlNCbQ33c0 f ξ) * hT + (tlNCbQ33c1 f ξ) * hT + (tlNCbQ33c2 f ξ) * hT + (tlNCbQ33c3 f ξ) * hT
      + (tlNCbQ33c4 f ξ) * hT + (tlNCbQ33c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP33c0, tlNCbP33c1, tlNCbP33c10, tlNCbP33c11,
      tlNCbP33c12, tlNCbP33c13, tlNCbP33c14, tlNCbP33c15, tlNCbP33c16, tlNCbP33c2,
      tlNCbP33c3, tlNCbP33c4, tlNCbP33c5, tlNCbP33c6, tlNCbP33c7, tlNCbP33c8,
      tlNCbP33c9, tlNCbQ33c0, tlNCbQ33c1, tlNCbQ33c2, tlNCbQ33c3, tlNCbQ33c4,
      tlNCbQ33c5, tlNSqP3c4, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP33c0 f ξ + tlNCbP33c1 f ξ) + (tlNCbP33c2 f ξ + tlNCbP33c3 f ξ)) +
        ((tlNCbP33c4 f ξ + tlNCbP33c5 f ξ) + (tlNCbP33c6 f ξ + tlNCbP33c7 f ξ))) +
        (((tlNCbP33c8 f ξ + tlNCbP33c9 f ξ) + (tlNCbP33c10 f ξ + tlNCbP33c11 f ξ)) +
        ((tlNCbP33c12 f ξ + tlNCbP33c13 f ξ) + (tlNCbP33c14 f ξ + tlNCbP33c15 f ξ)))) +
        tlNCbP33c16 f ξ) := by
  exact MazurTorsion.Kubert.tlNCb_s33

#print axioms solution
