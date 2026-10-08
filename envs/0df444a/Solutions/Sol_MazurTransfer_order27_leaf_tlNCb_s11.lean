-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s11
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:31:59.555649+00:00
-- url     : https://prove2.me/submissions/9d697e82-d41b-43a1-ab93-2972675ce7fe

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s11 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP11c0 f ξ + tlNCbP11c1 f ξ) + (tlNCbP11c2 f ξ + tlNCbP11c3 f ξ)) +
        ((tlNCbP11c4 f ξ + tlNCbP11c5 f ξ) + (tlNCbP11c6 f ξ + tlNCbP11c7 f ξ))) +
        (((tlNCbP11c8 f ξ + tlNCbP11c9 f ξ) + (tlNCbP11c10 f ξ + tlNCbP11c11 f ξ)) +
        ((tlNCbP11c12 f ξ + tlNCbP11c13 f ξ) + tlNCbP11c14 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ11c0 f ξ) * hT + (tlNCbQ11c1 f ξ) * hT + (tlNCbQ11c2 f ξ) * hT + (tlNCbQ11c3 f ξ) * hT
      + (tlNCbQ11c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP11c0, tlNCbP11c1, tlNCbP11c10, tlNCbP11c11,
      tlNCbP11c12, tlNCbP11c13, tlNCbP11c14, tlNCbP11c2, tlNCbP11c3, tlNCbP11c4,
      tlNCbP11c5, tlNCbP11c6, tlNCbP11c7, tlNCbP11c8, tlNCbP11c9, tlNCbQ11c0,
      tlNCbQ11c1, tlNCbQ11c2, tlNCbQ11c3, tlNCbQ11c4, tlNSqP1c3, tlT0, tlT1, tlT2,
      tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP11c0 f ξ + tlNCbP11c1 f ξ) + (tlNCbP11c2 f ξ + tlNCbP11c3 f ξ)) +
        ((tlNCbP11c4 f ξ + tlNCbP11c5 f ξ) + (tlNCbP11c6 f ξ + tlNCbP11c7 f ξ))) +
        (((tlNCbP11c8 f ξ + tlNCbP11c9 f ξ) + (tlNCbP11c10 f ξ + tlNCbP11c11 f ξ)) +
        ((tlNCbP11c12 f ξ + tlNCbP11c13 f ξ) + tlNCbP11c14 f ξ))) := by
  exact MazurTorsion.Kubert.tlNCb_s11

#print axioms solution
