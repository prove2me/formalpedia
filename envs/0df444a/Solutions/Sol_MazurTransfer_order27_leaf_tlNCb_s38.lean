-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s38
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:03.259574+00:00
-- url     : https://prove2.me/submissions/fbf30dbd-fce5-46bc-b5de-cd2237f0a6e3

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s38 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP38c0 f + tlNCbP38c1 f ξ) + (tlNCbP38c2 f ξ + tlNCbP38c3 f ξ)) +
        ((tlNCbP38c4 f ξ + tlNCbP38c5 f ξ) + (tlNCbP38c6 f ξ + tlNCbP38c7 f ξ))) +
        (((tlNCbP38c8 f ξ + tlNCbP38c9 f ξ) + (tlNCbP38c10 f ξ + tlNCbP38c11 f ξ)) +
        ((tlNCbP38c12 f ξ + tlNCbP38c13 f ξ) + (tlNCbP38c14 f ξ + tlNCbP38c15 f ξ)))) +
        ((tlNCbP38c16 f ξ + tlNCbP38c17 f ξ) + tlNCbP38c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ38c0 f ξ) * hT + (tlNCbQ38c1 f ξ) * hT + (tlNCbQ38c2 f ξ) * hT + (tlNCbQ38c3 f ξ) * hT
      + (tlNCbQ38c4 f ξ) * hT + (tlNCbQ38c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP38c0, tlNCbP38c1, tlNCbP38c10, tlNCbP38c11,
      tlNCbP38c12, tlNCbP38c13, tlNCbP38c14, tlNCbP38c15, tlNCbP38c16, tlNCbP38c17,
      tlNCbP38c18, tlNCbP38c2, tlNCbP38c3, tlNCbP38c4, tlNCbP38c5, tlNCbP38c6,
      tlNCbP38c7, tlNCbP38c8, tlNCbP38c9, tlNCbQ38c0, tlNCbQ38c1, tlNCbQ38c2,
      tlNCbQ38c3, tlNCbQ38c4, tlNCbQ38c5, tlNSqP3c9, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP38c0 f + tlNCbP38c1 f ξ) + (tlNCbP38c2 f ξ + tlNCbP38c3 f ξ)) +
        ((tlNCbP38c4 f ξ + tlNCbP38c5 f ξ) + (tlNCbP38c6 f ξ + tlNCbP38c7 f ξ))) +
        (((tlNCbP38c8 f ξ + tlNCbP38c9 f ξ) + (tlNCbP38c10 f ξ + tlNCbP38c11 f ξ)) +
        ((tlNCbP38c12 f ξ + tlNCbP38c13 f ξ) + (tlNCbP38c14 f ξ + tlNCbP38c15 f ξ)))) +
        ((tlNCbP38c16 f ξ + tlNCbP38c17 f ξ) + tlNCbP38c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s38

#print axioms solution
