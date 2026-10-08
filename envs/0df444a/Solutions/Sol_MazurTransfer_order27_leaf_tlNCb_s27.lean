-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s27
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:37:20.052615+00:00
-- url     : https://prove2.me/submissions/dba9e9a8-1487-4a23-819e-19c6e4ff5430

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s27 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP27c0 f ξ + tlNCbP27c1 f ξ) + (tlNCbP27c2 f ξ + tlNCbP27c3 f ξ)) +
        ((tlNCbP27c4 f ξ + tlNCbP27c5 f ξ) + (tlNCbP27c6 f ξ + tlNCbP27c7 f ξ))) +
        (((tlNCbP27c8 f ξ + tlNCbP27c9 f ξ) + (tlNCbP27c10 f ξ + tlNCbP27c11 f ξ)) +
        ((tlNCbP27c12 f ξ + tlNCbP27c13 f ξ) + (tlNCbP27c14 f ξ + tlNCbP27c15 f ξ)))) +
        ((tlNCbP27c16 f ξ + tlNCbP27c17 f ξ) + tlNCbP27c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ27c0 f ξ) * hT + (tlNCbQ27c1 f ξ) * hT + (tlNCbQ27c2 f ξ) * hT + (tlNCbQ27c3 f ξ) * hT
      + (tlNCbQ27c4 f ξ) * hT + (tlNCbQ27c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP27c0, tlNCbP27c1, tlNCbP27c10, tlNCbP27c11,
      tlNCbP27c12, tlNCbP27c13, tlNCbP27c14, tlNCbP27c15, tlNCbP27c16, tlNCbP27c17,
      tlNCbP27c18, tlNCbP27c2, tlNCbP27c3, tlNCbP27c4, tlNCbP27c5, tlNCbP27c6,
      tlNCbP27c7, tlNCbP27c8, tlNCbP27c9, tlNCbQ27c0, tlNCbQ27c1, tlNCbQ27c2,
      tlNCbQ27c3, tlNCbQ27c4, tlNCbQ27c5, tlNSqP2c9, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP27c0 f ξ + tlNCbP27c1 f ξ) + (tlNCbP27c2 f ξ + tlNCbP27c3 f ξ)) +
        ((tlNCbP27c4 f ξ + tlNCbP27c5 f ξ) + (tlNCbP27c6 f ξ + tlNCbP27c7 f ξ))) +
        (((tlNCbP27c8 f ξ + tlNCbP27c9 f ξ) + (tlNCbP27c10 f ξ + tlNCbP27c11 f ξ)) +
        ((tlNCbP27c12 f ξ + tlNCbP27c13 f ξ) + (tlNCbP27c14 f ξ + tlNCbP27c15 f ξ)))) +
        ((tlNCbP27c16 f ξ + tlNCbP27c17 f ξ) + tlNCbP27c18 f ξ)) := by
  exact MazurTorsion.Kubert.tlNCb_s27

#print axioms solution
