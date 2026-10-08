-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:37.949988+00:00
-- url     : https://prove2.me/submissions/fe5dab6f-2d1f-490f-8060-c5dbe331886e

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

lemma zlTNTDSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        zlTNTDSqP0c4 f Z := by
  linear_combination (norm := skip)
    (zlTNTDSqQ0c0 f Z) * hM + (zlTNTDSqQ0c1 f Z) * hM + (zlTNTDSqQ0c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP0c0, zlTNTDP0c1,
      zlTNTDSqP0c0, zlTNTDSqP0c1, zlTNTDSqP0c2, zlTNTDSqP0c3, zlTNTDSqP0c4,
      zlTNTDSqQ0c0, zlTNTDSqQ0c1, zlTNTDSqQ0c2]
  ring1

lemma zlTNTDSq_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z + zlTNTDP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z) + (zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z)) +
        (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z) := by
  linear_combination (norm := skip)
    (zlTNTDSqQ1c0 f Z) * hM + (zlTNTDSqQ1c1 f Z) * hM + (zlTNTDSqQ1c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP0c2, zlTNTDP0c3, zlTNTDP0c4,
      zlTNTDSqP1c0, zlTNTDSqP1c1, zlTNTDSqP1c2, zlTNTDSqP1c3, zlTNTDSqP1c4,
      zlTNTDSqP1c5, zlTNTDSqQ1c0, zlTNTDSqQ1c1, zlTNTDSqQ1c2]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        zlTNTDSqP0c4 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP0c2 f Z + zlTNTDP0c3 f Z + zlTNTDP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z) + (zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z)) +
        (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z)) := by
  exact ⟨MazurTorsion.Kubert.zlTNTDSq_s0, MazurTorsion.Kubert.zlTNTDSq_s1⟩

#print axioms MazurTransfer.order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        zlTNTDSqP0c4 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP0c2 f Z + zlTNTDP0c3 f Z + zlTNTDP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z) + (zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z)) +
        (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z))  := by
  exact MazurTransfer.order27_certificate_zlTNTDSq_s0_zlTNTDSq_s1

#print axioms solution
