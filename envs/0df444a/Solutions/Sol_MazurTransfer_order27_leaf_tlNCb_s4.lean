-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:28:27.098883+00:00
-- url     : https://prove2.me/submissions/2aff390e-833c-47ab-89d9-78fd61eef230

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP4c0 f ξ + tlNCbP4c1 f ξ) + (tlNCbP4c2 f ξ + tlNCbP4c3 f ξ)) + ((tlNCbP4c4
        f ξ + tlNCbP4c5 f ξ) + (tlNCbP4c6 f ξ + tlNCbP4c7 f ξ))) + (((tlNCbP4c8 f ξ +
        tlNCbP4c9 f ξ) + (tlNCbP4c10 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP4c12 f ξ +
        tlNCbP4c13 f ξ) + (tlNCbP4c14 f ξ + tlNCbP4c15 f ξ)))) + tlNCbP4c16 f ξ := by
  linear_combination (norm := skip)
    (tlNCbQ4c0 f ξ) * hT + (tlNCbQ4c1 f ξ) * hT + (tlNCbQ4c2 f ξ) * hT + (tlNCbQ4c3 f ξ) * hT +
      (tlNCbQ4c4 f ξ) * hT + (tlNCbQ4c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP4c0, tlNCbP4c1, tlNCbP4c10, tlNCbP4c11,
      tlNCbP4c12, tlNCbP4c13, tlNCbP4c14, tlNCbP4c15, tlNCbP4c16, tlNCbP4c2,
      tlNCbP4c3, tlNCbP4c4, tlNCbP4c5, tlNCbP4c6, tlNCbP4c7, tlNCbP4c8, tlNCbP4c9,
      tlNCbQ4c0, tlNCbQ4c1, tlNCbQ4c2, tlNCbQ4c3, tlNCbQ4c4, tlNCbQ4c5, tlNSqP0c4,
      tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP4c0 f ξ + tlNCbP4c1 f ξ) + (tlNCbP4c2 f ξ + tlNCbP4c3 f ξ)) + ((tlNCbP4c4
        f ξ + tlNCbP4c5 f ξ) + (tlNCbP4c6 f ξ + tlNCbP4c7 f ξ))) + (((tlNCbP4c8 f ξ +
        tlNCbP4c9 f ξ) + (tlNCbP4c10 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP4c12 f ξ +
        tlNCbP4c13 f ξ) + (tlNCbP4c14 f ξ + tlNCbP4c15 f ξ)))) + tlNCbP4c16 f ξ) := by
  exact MazurTorsion.Kubert.tlNCb_s4

#print axioms solution
