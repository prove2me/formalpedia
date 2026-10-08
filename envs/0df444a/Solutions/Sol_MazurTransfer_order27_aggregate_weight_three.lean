-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_weight_three
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:15.655763+00:00
-- url     : https://prove2.me/submissions/4857072c-c993-4e6d-a8be-e63f21b0ab7a

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.WeightsHigh. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# High-degree weighted third-leg identities

The cubic and quadratic coefficient-weighted identities used in the final
Fricke-twisted correspondence certificate.
-/



section

namespace MazurTorsion.Kubert

lemma zlWThree_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNCbP0c0 f + zlTNCbP0c1 f + zlTNCbP0c2 f) * zlCThree0 f =
      (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCThree0, zlTNCbP0c0, zlTNCbP0c1, zlTNCbP0c2, zlWThreeP0c0,
      zlWThreeP0c1, zlWThreeP0c2, zlWThreeP0c3]
  ring1

lemma zlWThree_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f) * zlCThree0 f =
      (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) := by
  linear_combination
    (zlWThree_s0 hM)





end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f) * zlCThree0 f =
      (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f))
 := by
  exact MazurTorsion.Kubert.zlWThree_val

#print axioms solution

end
