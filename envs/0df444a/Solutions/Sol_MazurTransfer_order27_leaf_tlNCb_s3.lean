-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:29:00.952334+00:00
-- url     : https://prove2.me/submissions/349896db-0bfb-4b6e-bf83-f712e6aec7bb

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP3c0 f ξ + tlNCbP3c1 f ξ) + (tlNCbP3c2 f ξ + tlNCbP3c3 f ξ)) + ((tlNCbP3c4 f
        ξ + tlNCbP3c5 f ξ) + (tlNCbP3c6 f ξ + tlNCbP3c7 f ξ))) + (((tlNCbP3c8 f ξ +
        tlNCbP3c9 f ξ) + (tlNCbP3c10 f ξ + tlNCbP3c11 f ξ)) + ((tlNCbP3c12 f ξ +
        tlNCbP3c13 f ξ) + (tlNCbP3c14 f ξ + tlNCbP3c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ3c0 f ξ) * hT + (tlNCbQ3c1 f ξ) * hT + (tlNCbQ3c2 f ξ) * hT + (tlNCbQ3c3 f ξ) * hT +
      (tlNCbQ3c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP3c0, tlNCbP3c1, tlNCbP3c10, tlNCbP3c11,
      tlNCbP3c12, tlNCbP3c13, tlNCbP3c14, tlNCbP3c15, tlNCbP3c2, tlNCbP3c3,
      tlNCbP3c4, tlNCbP3c5, tlNCbP3c6, tlNCbP3c7, tlNCbP3c8, tlNCbP3c9, tlNCbQ3c0,
      tlNCbQ3c1, tlNCbQ3c2, tlNCbQ3c3, tlNCbQ3c4, tlNSqP0c3, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP3c0 f ξ + tlNCbP3c1 f ξ) + (tlNCbP3c2 f ξ + tlNCbP3c3 f ξ)) + ((tlNCbP3c4 f
        ξ + tlNCbP3c5 f ξ) + (tlNCbP3c6 f ξ + tlNCbP3c7 f ξ))) + (((tlNCbP3c8 f ξ +
        tlNCbP3c9 f ξ) + (tlNCbP3c10 f ξ + tlNCbP3c11 f ξ)) + ((tlNCbP3c12 f ξ +
        tlNCbP3c13 f ξ) + (tlNCbP3c14 f ξ + tlNCbP3c15 f ξ)))) := by
  exact MazurTorsion.Kubert.tlNCb_s3

#print axioms solution
