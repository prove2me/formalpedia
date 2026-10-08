-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s29
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:22.538794+00:00
-- url     : https://prove2.me/submissions/48631596-a0b3-45c1-ab21-d2c2843aa64f

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s29 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP29c0 f ξ + tlNCbP29c1 f ξ) + (tlNCbP29c2 f ξ + tlNCbP29c3 f ξ)) +
        ((tlNCbP29c4 f ξ + tlNCbP29c5 f ξ) + (tlNCbP29c6 f ξ + tlNCbP29c7 f ξ))) +
        ((tlNCbP29c8 f ξ + tlNCbP29c9 f ξ) + tlNCbP29c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ29c0 f ξ) * hT + (tlNCbQ29c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP29c0, tlNCbP29c1, tlNCbP29c10, tlNCbP29c2,
      tlNCbP29c3, tlNCbP29c4, tlNCbP29c5, tlNCbP29c6, tlNCbP29c7, tlNCbP29c8,
      tlNCbP29c9, tlNCbQ29c0, tlNCbQ29c1, tlNSqP3c0, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP29c0 f ξ + tlNCbP29c1 f ξ) + (tlNCbP29c2 f ξ + tlNCbP29c3 f ξ)) +
        ((tlNCbP29c4 f ξ + tlNCbP29c5 f ξ) + (tlNCbP29c6 f ξ + tlNCbP29c7 f ξ))) +
        ((tlNCbP29c8 f ξ + tlNCbP29c9 f ξ) + tlNCbP29c10 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s29

#print axioms solution
