-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:19.557974+00:00
-- url     : https://prove2.me/submissions/7d8ac4aa-c0ea-4ed6-94f3-f1642363f137

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.WeightZero. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Constant weighted third-leg identity

The constant coefficient-weighted identity used in the final Fricke-twisted
correspondence certificate.
-/



section

namespace MazurTorsion.Kubert

lemma zlWZero_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDCbP0c0 f Z + zlTDCbP0c1 f Z + zlTDCbP0c2 f Z + zlTDCbP0c3 f Z + zlTDCbP0c4 f Z +
      zlTDCbP1c0 f Z + zlTDCbP1c1 f Z + zlTDCbP1c2 f Z) * zlCZero0 f =
      ((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) +
        ((zlWZeroP0c4 f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z)) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCZero0, zlTDCbP0c0, zlTDCbP0c1, zlTDCbP0c2, zlTDCbP0c3,
      zlTDCbP0c4, zlTDCbP1c0, zlTDCbP1c1, zlTDCbP1c2, zlWZeroP0c0, zlWZeroP0c1,
      zlWZeroP0c2, zlWZeroP0c3, zlWZeroP0c4, zlWZeroP0c5, zlWZeroP0c6, zlWZeroP0c7]
  ring1

lemma zlWZero_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDCbP1c3 f Z + zlTDCbP1c4 f Z + zlTDCbP1c5 f Z) * zlCZero0 f =
      ((zlWZeroP1c0 f Z + zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) +
        zlWZeroP1c4 f Z := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCZero0, zlTDCbP1c3, zlTDCbP1c4, zlTDCbP1c5, zlWZeroP1c0,
      zlWZeroP1c1, zlWZeroP1c2, zlWZeroP1c3, zlWZeroP1c4]
  ring1

lemma zlWZero_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + ((zlTDCbP0c4 f Z +
      zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) + ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) +
      zlTDCbP1c5 f Z)) * zlCZero0 f =
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) +
        ((zlWZeroP0c4 f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) +
        (((zlWZeroP1c0 f Z + zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) +
        zlWZeroP1c4 f Z) := by
  linear_combination
    (zlWZero_s0 hM) + (zlWZero_s1 hM)

end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + ((zlTDCbP0c4 f Z +
      zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) + ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) +
      zlTDCbP1c5 f Z)) * zlCZero0 f =
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) +
        ((zlWZeroP0c4 f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) +
        (((zlWZeroP1c0 f Z + zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) +
        zlWZeroP1c4 f Z))
 := by
  exact MazurTorsion.Kubert.zlWZero_val

#print axioms solution

end
