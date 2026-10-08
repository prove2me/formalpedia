-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s32
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:28.308701+00:00
-- url     : https://prove2.me/submissions/77d60f53-6fda-431f-9c8e-9c419a477fa0

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s32 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP32c0 f ξ + tlNCbP32c1 f ξ) + (tlNCbP32c2 f ξ + tlNCbP32c3 f ξ)) +
        ((tlNCbP32c4 f ξ + tlNCbP32c5 f ξ) + (tlNCbP32c6 f ξ + tlNCbP32c7 f ξ))) +
        (((tlNCbP32c8 f ξ + tlNCbP32c9 f ξ) + (tlNCbP32c10 f ξ + tlNCbP32c11 f ξ)) +
        ((tlNCbP32c12 f ξ + tlNCbP32c13 f ξ) + (tlNCbP32c14 f ξ + tlNCbP32c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ32c0 f ξ) * hT + (tlNCbQ32c1 f ξ) * hT + (tlNCbQ32c2 f ξ) * hT + (tlNCbQ32c3 f ξ) * hT
      + (tlNCbQ32c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP32c0, tlNCbP32c1, tlNCbP32c10, tlNCbP32c11,
      tlNCbP32c12, tlNCbP32c13, tlNCbP32c14, tlNCbP32c15, tlNCbP32c2, tlNCbP32c3,
      tlNCbP32c4, tlNCbP32c5, tlNCbP32c6, tlNCbP32c7, tlNCbP32c8, tlNCbP32c9,
      tlNCbQ32c0, tlNCbQ32c1, tlNCbQ32c2, tlNCbQ32c3, tlNCbQ32c4, tlNSqP3c3, tlT0,
      tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP32c0 f ξ + tlNCbP32c1 f ξ) + (tlNCbP32c2 f ξ + tlNCbP32c3 f ξ)) +
        ((tlNCbP32c4 f ξ + tlNCbP32c5 f ξ) + (tlNCbP32c6 f ξ + tlNCbP32c7 f ξ))) +
        (((tlNCbP32c8 f ξ + tlNCbP32c9 f ξ) + (tlNCbP32c10 f ξ + tlNCbP32c11 f ξ)) +
        ((tlNCbP32c12 f ξ + tlNCbP32c13 f ξ) + (tlNCbP32c14 f ξ + tlNCbP32c15 f ξ)))) := by
  exact MazurTorsion.Kubert.tlNCb_s32

#print axioms solution
