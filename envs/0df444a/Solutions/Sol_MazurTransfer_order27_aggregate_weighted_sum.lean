-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:21.46638+00:00
-- url     : https://prove2.me/submissions/8962f964-8708-419d-b464-48e6a87a0d2c

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.ZeroSum. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Third-leg weighted zero sum

The expanded weighted certificate terms sum to zero before the final staged
combination.
-/



section

namespace MazurTorsion.Kubert

lemma zl_zeroZ (f Z : ℚ) :
    (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) + (((zlWTwoP0c0 f Z +
      zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) + ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) +
      (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) + (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z) + ((((zlWOneP0c0 f Z
      + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) + ((zlWOneP0c4 f Z + zlWOneP0c5 f Z)
      + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) + (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f
      Z + zlWOneP1c2 f Z)) + ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f
      Z)))) + ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
      ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) + zlWOneP2c5 f Z) +
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) + ((zlWZeroP0c4
      f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) + (((zlWZeroP1c0 f Z +
      zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) + zlWZeroP1c4 f Z) = 0 := by
  simp only [zlWThreeP0c0, zlWThreeP0c1, zlWThreeP0c2, zlWThreeP0c3, zlWTwoP0c0, zlWTwoP0c1,
      zlWTwoP0c2, zlWTwoP0c3, zlWTwoP0c4, zlWTwoP0c5, zlWTwoP0c6, zlWTwoP0c7,
      zlWTwoP0c8, zlWTwoP0c9, zlWOneP0c0, zlWOneP0c1, zlWOneP0c2, zlWOneP0c3,
      zlWOneP0c4, zlWOneP0c5, zlWOneP0c6, zlWOneP0c7, zlWOneP0c8, zlWOneP1c0,
      zlWOneP1c1, zlWOneP1c2, zlWOneP1c3, zlWOneP1c4, zlWOneP1c5, zlWOneP1c6,
      zlWOneP1c7, zlWOneP1c8, zlWOneP1c9, zlWOneP2c0, zlWOneP2c1, zlWOneP2c2,
      zlWOneP2c3, zlWOneP2c4, zlWOneP2c5, zlWZeroP0c0, zlWZeroP0c1, zlWZeroP0c2,
      zlWZeroP0c3, zlWZeroP0c4, zlWZeroP0c5, zlWZeroP0c6, zlWZeroP0c7, zlWZeroP1c0,
      zlWZeroP1c1, zlWZeroP1c2, zlWZeroP1c3, zlWZeroP1c4]
  ring1

end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ (f Z : ℚ),
(zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) + (((zlWTwoP0c0 f Z +
      zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) + ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) +
      (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) + (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z) + ((((zlWOneP0c0 f Z
      + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) + ((zlWOneP0c4 f Z + zlWOneP0c5 f Z)
      + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) + (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f
      Z + zlWOneP1c2 f Z)) + ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f
      Z)))) + ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
      ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) + zlWOneP2c5 f Z) +
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) + ((zlWZeroP0c4
      f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) + (((zlWZeroP1c0 f Z +
      zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) + zlWZeroP1c4 f Z) = 0)
 := by
  exact MazurTorsion.Kubert.zl_zeroZ

#print axioms solution

end
