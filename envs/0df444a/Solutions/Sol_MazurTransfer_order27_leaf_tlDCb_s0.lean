-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlDCb_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:41:37.512485+00:00
-- url     : https://prove2.me/submissions/0db649cd-83e7-4c02-a88d-c8ae46fce4df

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlDCb_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c0 f ξ + tlDSqP0c1 f ξ + tlDSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f
        ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ) := by
  linear_combination (norm := skip)
    (tlDCbQ0c0 f ξ) * hT + (tlDCbQ0c1 f ξ) * hT + (tlDCbQ0c2 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP0c0, tlDCbP0c1, tlDCbP0c2, tlDCbP0c3, tlDCbP0c4, tlDCbP0c5,
      tlDCbP0c6, tlDCbP0c7, tlDCbP0c8, tlDCbP0c9, tlDCbQ0c0, tlDCbQ0c1, tlDCbQ0c2,
      tlDSqP0c0, tlDSqP0c1, tlDSqP0c2, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c0 f ξ + tlDSqP0c1 f ξ + tlDSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f
        ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ)) := by
  exact MazurTorsion.Kubert.tlDCb_s0

#print axioms solution
