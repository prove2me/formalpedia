-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlDCb_s2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:44:39.629993+00:00
-- url     : https://prove2.me/submissions/4febd787-6812-4561-95a4-c70234fbb993

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlDCb_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ + tlDSqP0c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP2c0 f ξ + tlDCbP2c1 f ξ) + (tlDCbP2c2 f ξ + tlDCbP2c3 f ξ)) + ((tlDCbP2c4 f
        ξ + tlDCbP2c5 f ξ) + (tlDCbP2c6 f ξ + tlDCbP2c7 f ξ))) + (((tlDCbP2c8 f ξ +
        tlDCbP2c9 f ξ) + (tlDCbP2c10 f ξ + tlDCbP2c11 f ξ)) + (tlDCbP2c12 f ξ + tlDCbP2c13
        f ξ)) := by
  linear_combination (norm := skip)
    (tlDCbQ2c0 f ξ) * hT + (tlDCbQ2c1 f ξ) * hT + (tlDCbQ2c2 f ξ) * hT + (tlDCbQ2c3 f ξ) * hT +
      (tlDCbQ2c4 f ξ) * hT + (tlDCbQ2c5 f ξ) * hT + (tlDCbQ2c6 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP2c0, tlDCbP2c1, tlDCbP2c10, tlDCbP2c11, tlDCbP2c12,
      tlDCbP2c13, tlDCbP2c2, tlDCbP2c3, tlDCbP2c4, tlDCbP2c5, tlDCbP2c6, tlDCbP2c7,
      tlDCbP2c8, tlDCbP2c9, tlDCbQ2c0, tlDCbQ2c1, tlDCbQ2c2, tlDCbQ2c3, tlDCbQ2c4,
      tlDCbQ2c5, tlDCbQ2c6, tlDSqP0c6, tlDSqP0c7, tlDSqP0c8, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c6 f ξ + tlDSqP0c7 f ξ + tlDSqP0c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP2c0 f ξ + tlDCbP2c1 f ξ) + (tlDCbP2c2 f ξ + tlDCbP2c3 f ξ)) + ((tlDCbP2c4 f
        ξ + tlDCbP2c5 f ξ) + (tlDCbP2c6 f ξ + tlDCbP2c7 f ξ))) + (((tlDCbP2c8 f ξ +
        tlDCbP2c9 f ξ) + (tlDCbP2c10 f ξ + tlDCbP2c11 f ξ)) + (tlDCbP2c12 f ξ + tlDCbP2c13
        f ξ))) := by
  exact MazurTorsion.Kubert.tlDCb_s2

#print axioms solution
