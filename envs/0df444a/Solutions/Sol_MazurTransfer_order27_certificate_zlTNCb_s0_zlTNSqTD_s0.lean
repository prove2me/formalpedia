-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:31.327046+00:00
-- url     : https://prove2.me/submissions/372892f0-c294-4cf3-84ef-b98cbcb05b46

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.Kubert

lemma zlTNCb_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f := by
  linear_combination (norm := skip)
    (zlTNCbQ0c0 f Z) * hM + (zlTNCbQ0c1 f Z) * hM + (zlTNCbQ0c2 f Z) * hM + (zlTNCbQ0c3 f Z) * hM
      + (zlTNCbQ0c4 f Z) * hM + (zlTNCbQ0c5 f Z) * hM + (zlTNCbQ0c6 f Z) * hM + (zlTNCbQ0c7 f Z) *
      hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNCbP0c0, zlTNCbP0c1, zlTNCbP0c2,
      zlTNCbQ0c0, zlTNCbQ0c1, zlTNCbQ0c2, zlTNCbQ0c3, zlTNCbQ0c4, zlTNCbQ0c5,
      zlTNCbQ0c6, zlTNCbQ0c7, zlTNSqP0c0, zlTNSqP0c1, zlTNSqP0c2, zlTNSqP0c3,
      zlTNSqP1c0, zlTNSqP1c1, zlTNSqP1c2, zlTNSqP1c3, zlTNSqP1c4, zlTNSqP2c0,
      zlTNSqP2c1, zlTNSqP2c2, zlTNSqP2c3, zlTNSqP2c4]
  ring1

lemma zlTNSqTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z)) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNSqP0c0, zlTNSqP0c1, zlTNSqP0c2,
      zlTNSqP0c3, zlTNSqP1c0, zlTNSqP1c1, zlTNSqP1c2, zlTNSqP1c3, zlTNSqP1c4,
      zlTNSqP2c0, zlTNSqP2c1, zlTNSqP2c2, zlTNSqP2c3, zlTNSqP2c4, zlTNSqTDP0c0,
      zlTNSqTDP0c1, zlTNSqTDP0c2, zlTNSqTDP0c3, zlTNSqTDP0c4, zlTNSqTDP0c5,
      zlTNSqTDP0c6, zlTNSqTDP0c7]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) := by
  exact ⟨MazurTorsion.Kubert.zlTNCb_s0, MazurTorsion.Kubert.zlTNSqTD_s0⟩

#print axioms MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z)))  := by
  exact MazurTransfer.order27_certificate_zlTNCb_s0_zlTNSqTD_s0

#print axioms solution
