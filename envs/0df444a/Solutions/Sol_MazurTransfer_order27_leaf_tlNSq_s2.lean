-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNSq_s2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:32:19.729817+00:00
-- url     : https://prove2.me/submissions/52d6c154-34a4-4075-8782-a7f1892d5d0e

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlNSq_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP2c0 f ξ + tlNSqP2c1 f ξ) + (tlNSqP2c2 f ξ + tlNSqP2c3 f ξ)) + ((tlNSqP2c4 f
        ξ + tlNSqP2c5 f ξ) + (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ))) + ((tlNSqP2c8 f ξ +
        tlNSqP2c9 f ξ) + (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlNSqQ2c0 f ξ) * hT + (tlNSqQ2c1 f ξ) * hT + (tlNSqQ2c2 f ξ) * hT + (tlNSqQ2c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP2c0, tlNSqP2c1, tlNSqP2c10, tlNSqP2c11, tlNSqP2c2,
      tlNSqP2c3, tlNSqP2c4, tlNSqP2c5, tlNSqP2c6, tlNSqP2c7, tlNSqP2c8, tlNSqP2c9,
      tlNSqQ2c0, tlNSqQ2c1, tlNSqQ2c2, tlNSqQ2c3, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP2c0 f ξ + tlNSqP2c1 f ξ) + (tlNSqP2c2 f ξ + tlNSqP2c3 f ξ)) + ((tlNSqP2c4 f
        ξ + tlNSqP2c5 f ξ) + (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ))) + ((tlNSqP2c8 f ξ +
        tlNSqP2c9 f ξ) + (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ))) := by
  exact MazurTorsion.Kubert.tlNSq_s2

#print axioms solution
