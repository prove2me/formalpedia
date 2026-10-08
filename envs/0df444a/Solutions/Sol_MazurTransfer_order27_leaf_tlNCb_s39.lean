-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s39
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:39:04.748988+00:00
-- url     : https://prove2.me/submissions/5b2ec76a-37bf-46da-9d77-5b0fc293534c

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s39 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c10 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP39c0 f + tlNCbP39c1 f ξ) + (tlNCbP39c2 f ξ + tlNCbP39c3 f ξ)) +
        ((tlNCbP39c4 f ξ + tlNCbP39c5 f ξ) + (tlNCbP39c6 f ξ + tlNCbP39c7 f ξ))) +
        (((tlNCbP39c8 f ξ + tlNCbP39c9 f ξ) + (tlNCbP39c10 f ξ + tlNCbP39c11 f ξ)) +
        ((tlNCbP39c12 f ξ + tlNCbP39c13 f ξ) + (tlNCbP39c14 f ξ + tlNCbP39c15 f ξ)))) +
        ((tlNCbP39c16 f ξ + tlNCbP39c17 f ξ) + tlNCbP39c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ39c0 f ξ) * hT + (tlNCbQ39c1 f ξ) * hT + (tlNCbQ39c2 f ξ) * hT + (tlNCbQ39c3 f ξ) * hT
      + (tlNCbQ39c4 f ξ) * hT + (tlNCbQ39c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP39c0, tlNCbP39c1, tlNCbP39c10, tlNCbP39c11,
      tlNCbP39c12, tlNCbP39c13, tlNCbP39c14, tlNCbP39c15, tlNCbP39c16, tlNCbP39c17,
      tlNCbP39c18, tlNCbP39c2, tlNCbP39c3, tlNCbP39c4, tlNCbP39c5, tlNCbP39c6,
      tlNCbP39c7, tlNCbP39c8, tlNCbP39c9, tlNCbQ39c0, tlNCbQ39c1, tlNCbQ39c2,
      tlNCbQ39c3, tlNCbQ39c4, tlNCbQ39c5, tlNSqP3c10, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c10 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP39c0 f + tlNCbP39c1 f ξ) + (tlNCbP39c2 f ξ + tlNCbP39c3 f ξ)) +
        ((tlNCbP39c4 f ξ + tlNCbP39c5 f ξ) + (tlNCbP39c6 f ξ + tlNCbP39c7 f ξ))) +
        (((tlNCbP39c8 f ξ + tlNCbP39c9 f ξ) + (tlNCbP39c10 f ξ + tlNCbP39c11 f ξ)) +
        ((tlNCbP39c12 f ξ + tlNCbP39c13 f ξ) + (tlNCbP39c14 f ξ + tlNCbP39c15 f ξ)))) +
        ((tlNCbP39c16 f ξ + tlNCbP39c17 f ξ) + tlNCbP39c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s39

#print axioms solution
