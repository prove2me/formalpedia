-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:17.430023+00:00
-- url     : https://prove2.me/submissions/9d9896cb-41f8-445a-9a4f-b4aad846be2d

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s13 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ)) +
        ((tlNCbP13c4 f ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ))) +
        (((tlNCbP13c8 f ξ + tlNCbP13c9 f ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)) +
        ((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) + (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)))) +
        (tlNCbP13c16 f ξ + tlNCbP13c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ13c0 f ξ) * hT + (tlNCbQ13c1 f ξ) * hT + (tlNCbQ13c2 f ξ) * hT + (tlNCbQ13c3 f ξ) * hT
      + (tlNCbQ13c4 f ξ) * hT + (tlNCbQ13c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP13c0, tlNCbP13c1, tlNCbP13c10, tlNCbP13c11,
      tlNCbP13c12, tlNCbP13c13, tlNCbP13c14, tlNCbP13c15, tlNCbP13c16, tlNCbP13c17,
      tlNCbP13c2, tlNCbP13c3, tlNCbP13c4, tlNCbP13c5, tlNCbP13c6, tlNCbP13c7,
      tlNCbP13c8, tlNCbP13c9, tlNCbQ13c0, tlNCbQ13c1, tlNCbQ13c2, tlNCbQ13c3,
      tlNCbQ13c4, tlNCbQ13c5, tlNSqP1c5, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ)) +
        ((tlNCbP13c4 f ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ))) +
        (((tlNCbP13c8 f ξ + tlNCbP13c9 f ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)) +
        ((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) + (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)))) +
        (tlNCbP13c16 f ξ + tlNCbP13c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s13

#print axioms solution
