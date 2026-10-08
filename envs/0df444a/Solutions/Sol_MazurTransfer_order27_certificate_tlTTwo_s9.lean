-- Prove2me | solution 1 for MazurTransfer.order27_certificate_tlTTwo_s9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:18:07.614386+00:00
-- url     : https://prove2.me/submissions/0ba22e9f-0374-4dd5-8761-98c76f067196

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c9 f ξ + tlNSqP2c10 f ξ + tlNSqP2c11 f ξ + tlNSqP3c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      ((((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ)) +
        ((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ))) +
        (((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ)) +
        ((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)))) +
        (tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ9c0 f ξ) * hT + (tlTTwoQ9c1 f ξ) * hT + (tlTTwoQ9c2 f ξ) * hT + (tlTTwoQ9c3 f ξ) * hT
      + (tlTTwoQ9c4 f ξ) * hT + (tlTTwoQ9c5 f ξ) * hT + (tlTTwoQ9c6 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c10, tlNSqP2c11, tlNSqP2c9, tlNSqP3c0, tlT0, tlT1, tlT2,
      tlT3, tlTTwoP9c0, tlTTwoP9c1, tlTTwoP9c10, tlTTwoP9c11, tlTTwoP9c12,
      tlTTwoP9c13, tlTTwoP9c14, tlTTwoP9c15, tlTTwoP9c16, tlTTwoP9c17, tlTTwoP9c2,
      tlTTwoP9c3, tlTTwoP9c4, tlTTwoP9c5, tlTTwoP9c6, tlTTwoP9c7, tlTTwoP9c8,
      tlTTwoP9c9, tlTTwoQ9c0, tlTTwoQ9c1, tlTTwoQ9c2, tlTTwoQ9c3, tlTTwoQ9c4,
      tlTTwoQ9c5, tlTTwoQ9c6]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP2c9 f ξ + tlNSqP2c10 f ξ + tlNSqP2c11 f ξ + tlNSqP3c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      ((((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ)) +
        ((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ))) +
        (((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ)) +
        ((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)))) +
        (tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ)) := by
  exact MazurTorsion.Kubert.tlTTwo_s9

#print axioms solution
