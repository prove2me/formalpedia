-- Prove2me | solution 1 for MazurTransfer.order27_aggregate_weight_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:17.683402+00:00
-- url     : https://prove2.me/submissions/f70b6f28-c355-4242-a869-349d94cfc8ad

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.WeightOne. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Linear weighted third-leg identity

The linear coefficient-weighted identity used in the final Fricke-twisted
correspondence certificate.
-/



section

namespace MazurTorsion.Kubert

lemma zlWOne_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z + zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z + zlTNTDSqP0c4 f Z
      + zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z) * zlCOne0 f =
      (((zlWOneP0c0 f Z + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) +
        ((zlWOneP0c4 f Z + zlWOneP0c5 f Z) + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) +
        zlWOneP0c8 f Z := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCOne0, zlTNTDSqP0c0, zlTNTDSqP0c1, zlTNTDSqP0c2, zlTNTDSqP0c3,
      zlTNTDSqP0c4, zlTNTDSqP1c0, zlTNTDSqP1c1, zlTNTDSqP1c2, zlTNTDSqP1c3,
      zlWOneP0c0, zlWOneP0c1, zlWOneP0c2, zlWOneP0c3, zlWOneP0c4, zlWOneP0c5,
      zlWOneP0c6, zlWOneP0c7, zlWOneP0c8]
  ring1

lemma zlWOne_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z
      + zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z + zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z + zlTNTDSqP3c2 f
      Z) * zlCOne0 f =
      (((zlWOneP1c0 f Z + zlWOneP1c1 f Z) + (zlWOneP1c2 f Z + zlWOneP1c3 f Z)) +
        ((zlWOneP1c4 f Z + zlWOneP1c5 f Z) + (zlWOneP1c6 f Z + zlWOneP1c7 f Z))) +
        (zlWOneP1c8 f Z + zlWOneP1c9 f Z) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCOne0, zlTNTDSqP1c4, zlTNTDSqP1c5, zlTNTDSqP2c0, zlTNTDSqP2c1,
      zlTNTDSqP2c2, zlTNTDSqP2c3, zlTNTDSqP2c4, zlTNTDSqP3c0, zlTNTDSqP3c1,
      zlTNTDSqP3c2, zlWOneP1c0, zlWOneP1c1, zlWOneP1c2, zlWOneP1c3, zlWOneP1c4,
      zlWOneP1c5, zlWOneP1c6, zlWOneP1c7, zlWOneP1c8, zlWOneP1c9]
  ring1

lemma zlWOne_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDSqP3c3 f Z + zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z) * zlCOne0 f =
      ((zlWOneP2c0 f Z + zlWOneP2c1 f Z) + (zlWOneP2c2 f Z + zlWOneP2c3 f Z)) +
        (zlWOneP2c4 f Z + zlWOneP2c5 f Z) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCOne0, zlTNTDSqP3c3, zlTNTDSqP3c4, zlTNTDSqP3c5, zlWOneP2c0,
      zlWOneP2c1, zlWOneP2c2, zlWOneP2c3, zlWOneP2c4, zlWOneP2c5]
  ring1

lemma zlWOne_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
      ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
      (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
      ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z)))) +
      (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
      (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) * zlCOne0 f =
      ((((zlWOneP0c0 f Z + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) +
        ((zlWOneP0c4 f Z + zlWOneP0c5 f Z) + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) +
        (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f Z + zlWOneP1c2 f Z)) +
        ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f Z)))) +
        ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
        ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) +
        zlWOneP2c5 f Z) := by
  linear_combination
    ((zlWOne_s0 hM) + (zlWOne_s1 hM)) + (zlWOne_s2 hM)

end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
      ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
      (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
      ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z)))) +
      (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
      (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) * zlCOne0 f =
      ((((zlWOneP0c0 f Z + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) +
        ((zlWOneP0c4 f Z + zlWOneP0c5 f Z) + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) +
        (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f Z + zlWOneP1c2 f Z)) +
        ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f Z)))) +
        ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
        ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) +
        zlWOneP2c5 f Z))
 := by
  exact MazurTorsion.Kubert.zlWOne_val

#print axioms solution

end
