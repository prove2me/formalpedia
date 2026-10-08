-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s21
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:35:55.425476+00:00
-- url     : https://prove2.me/submissions/08983771-6226-4f61-b4ff-fb66f8d4fdce

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s21 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP21c0 f ξ + tlNCbP21c1 f ξ) + (tlNCbP21c2 f ξ + tlNCbP21c3 f ξ)) +
        ((tlNCbP21c4 f ξ + tlNCbP21c5 f ξ) + (tlNCbP21c6 f ξ + tlNCbP21c7 f ξ))) +
        (((tlNCbP21c8 f ξ + tlNCbP21c9 f ξ) + (tlNCbP21c10 f ξ + tlNCbP21c11 f ξ)) +
        ((tlNCbP21c12 f ξ + tlNCbP21c13 f ξ) + tlNCbP21c14 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ21c0 f ξ) * hT + (tlNCbQ21c1 f ξ) * hT + (tlNCbQ21c2 f ξ) * hT + (tlNCbQ21c3 f ξ) * hT
      + (tlNCbQ21c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP21c0, tlNCbP21c1, tlNCbP21c10, tlNCbP21c11,
      tlNCbP21c12, tlNCbP21c13, tlNCbP21c14, tlNCbP21c2, tlNCbP21c3, tlNCbP21c4,
      tlNCbP21c5, tlNCbP21c6, tlNCbP21c7, tlNCbP21c8, tlNCbP21c9, tlNCbQ21c0,
      tlNCbQ21c1, tlNCbQ21c2, tlNCbQ21c3, tlNCbQ21c4, tlNSqP2c3, tlT0, tlT1, tlT2,
      tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP21c0 f ξ + tlNCbP21c1 f ξ) + (tlNCbP21c2 f ξ + tlNCbP21c3 f ξ)) +
        ((tlNCbP21c4 f ξ + tlNCbP21c5 f ξ) + (tlNCbP21c6 f ξ + tlNCbP21c7 f ξ))) +
        (((tlNCbP21c8 f ξ + tlNCbP21c9 f ξ) + (tlNCbP21c10 f ξ + tlNCbP21c11 f ξ)) +
        ((tlNCbP21c12 f ξ + tlNCbP21c13 f ξ) + tlNCbP21c14 f ξ))) := by
  exact MazurTorsion.Kubert.tlNCb_s21

#print axioms solution
