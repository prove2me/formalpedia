-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlDCb_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:44:03.500715+00:00
-- url     : https://prove2.me/submissions/b18e9cc2-3430-48eb-9168-cf961f6a17f5

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma tlDCb_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) + (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ)) + ((tlDCbP3c4 f
        ξ + tlDCbP3c5 f ξ) + (tlDCbP3c6 f ξ + tlDCbP3c7 f ξ))) + ((tlDCbP3c8 f ξ +
        tlDCbP3c9 f ξ) + (tlDCbP3c10 f ξ + tlDCbP3c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlDCbQ3c0 f ξ) * hT + (tlDCbQ3c1 f ξ) * hT + (tlDCbQ3c2 f ξ) * hT + (tlDCbQ3c3 f ξ) * hT +
      (tlDCbQ3c4 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP3c0, tlDCbP3c1, tlDCbP3c10, tlDCbP3c11, tlDCbP3c2, tlDCbP3c3,
      tlDCbP3c4, tlDCbP3c5, tlDCbP3c6, tlDCbP3c7, tlDCbP3c8, tlDCbP3c9, tlDCbQ3c0,
      tlDCbQ3c1, tlDCbQ3c2, tlDCbQ3c3, tlDCbQ3c4, tlDSqP0c9, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert

theorem solution :
  (∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) + (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ)) + ((tlDCbP3c4 f
        ξ + tlDCbP3c5 f ξ) + (tlDCbP3c6 f ξ + tlDCbP3c7 f ξ))) + ((tlDCbP3c8 f ξ +
        tlDCbP3c9 f ξ) + (tlDCbP3c10 f ξ + tlDCbP3c11 f ξ))) := by
  exact MazurTorsion.Kubert.tlDCb_s3

#print axioms solution
