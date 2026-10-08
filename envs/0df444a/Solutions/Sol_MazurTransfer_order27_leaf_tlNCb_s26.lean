-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s26
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:38:05.377257+00:00
-- url     : https://prove2.me/submissions/99460111-6508-41d9-8485-e59efaa23de4

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s26 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ)) +
        ((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ))) +
        (((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ)) +
        ((tlNCbP26c12 f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)))) +
        ((tlNCbP26c16 f ξ + tlNCbP26c17 f ξ) + tlNCbP26c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ26c0 f ξ) * hT + (tlNCbQ26c1 f ξ) * hT + (tlNCbQ26c2 f ξ) * hT + (tlNCbQ26c3 f ξ) * hT
      + (tlNCbQ26c4 f ξ) * hT + (tlNCbQ26c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP26c0, tlNCbP26c1, tlNCbP26c10, tlNCbP26c11,
      tlNCbP26c12, tlNCbP26c13, tlNCbP26c14, tlNCbP26c15, tlNCbP26c16, tlNCbP26c17,
      tlNCbP26c18, tlNCbP26c2, tlNCbP26c3, tlNCbP26c4, tlNCbP26c5, tlNCbP26c6,
      tlNCbP26c7, tlNCbP26c8, tlNCbP26c9, tlNCbQ26c0, tlNCbQ26c1, tlNCbQ26c2,
      tlNCbQ26c3, tlNCbQ26c4, tlNCbQ26c5, tlNSqP2c8, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ)) +
        ((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ))) +
        (((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ)) +
        ((tlNCbP26c12 f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)))) +
        ((tlNCbP26c16 f ξ + tlNCbP26c17 f ξ) + tlNCbP26c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s26

#print axioms solution
