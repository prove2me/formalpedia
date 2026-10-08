-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s22
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:36:36.269546+00:00
-- url     : https://prove2.me/submissions/f182c7a4-c15c-472c-8653-5ee113fba166

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s22 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP22c0 f ξ + tlNCbP22c1 f ξ) + (tlNCbP22c2 f ξ + tlNCbP22c3 f ξ)) +
        ((tlNCbP22c4 f ξ + tlNCbP22c5 f ξ) + (tlNCbP22c6 f ξ + tlNCbP22c7 f ξ))) +
        (((tlNCbP22c8 f ξ + tlNCbP22c9 f ξ) + (tlNCbP22c10 f ξ + tlNCbP22c11 f ξ)) +
        ((tlNCbP22c12 f ξ + tlNCbP22c13 f ξ) + (tlNCbP22c14 f ξ + tlNCbP22c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ22c0 f ξ) * hT + (tlNCbQ22c1 f ξ) * hT + (tlNCbQ22c2 f ξ) * hT + (tlNCbQ22c3 f ξ) * hT
      + (tlNCbQ22c4 f ξ) * hT + (tlNCbQ22c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP22c0, tlNCbP22c1, tlNCbP22c10, tlNCbP22c11,
      tlNCbP22c12, tlNCbP22c13, tlNCbP22c14, tlNCbP22c15, tlNCbP22c2, tlNCbP22c3,
      tlNCbP22c4, tlNCbP22c5, tlNCbP22c6, tlNCbP22c7, tlNCbP22c8, tlNCbP22c9,
      tlNCbQ22c0, tlNCbQ22c1, tlNCbQ22c2, tlNCbQ22c3, tlNCbQ22c4, tlNCbQ22c5,
      tlNSqP2c4, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP22c0 f ξ + tlNCbP22c1 f ξ) + (tlNCbP22c2 f ξ + tlNCbP22c3 f ξ)) +
        ((tlNCbP22c4 f ξ + tlNCbP22c5 f ξ) + (tlNCbP22c6 f ξ + tlNCbP22c7 f ξ))) +
        (((tlNCbP22c8 f ξ + tlNCbP22c9 f ξ) + (tlNCbP22c10 f ξ + tlNCbP22c11 f ξ)) +
        ((tlNCbP22c12 f ξ + tlNCbP22c13 f ξ) + (tlNCbP22c14 f ξ + tlNCbP22c15 f ξ)))) := by
  exact MazurTorsion.Kubert.tlNCb_s22

#print axioms solution
