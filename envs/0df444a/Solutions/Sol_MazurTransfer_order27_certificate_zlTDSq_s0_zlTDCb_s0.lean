-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:33.710295+00:00
-- url     : https://prove2.me/submissions/ea9408d6-501c-41a5-8eb9-c4efbb0c7551

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

lemma zlTDSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z := by
  linear_combination (norm := skip)
    (zlTDSqQ0c0 f Z) * hM + (zlTDSqQ0c1 f Z) * hM + (zlTDSqQ0c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTDSqP0c0, zlTDSqP0c1, zlTDSqP0c2,
      zlTDSqP0c3, zlTDSqP0c4, zlTDSqQ0c0, zlTDSqQ0c1, zlTDSqQ0c2]
  ring1

lemma zlTDCb_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + zlTDCbP0c4
        f Z := by
  linear_combination (norm := skip)
    (zlTDCbQ0c0 f Z) * hM + (zlTDCbQ0c1 f Z) * hM + (zlTDCbQ0c2 f Z) * hM
  simp only [kernelCubicM, zlTDCbP0c0, zlTDCbP0c1, zlTDCbP0c2, zlTDCbP0c3, zlTDCbP0c4,
      zlTDCbQ0c0, zlTDCbQ0c1, zlTDCbQ0c2, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTDSqP0c0,
      zlTDSqP0c1]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + zlTDCbP0c4
        f Z) := by
  exact ⟨MazurTorsion.Kubert.zlTDSq_s0, MazurTorsion.Kubert.zlTDCb_s0⟩

#print axioms MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + zlTDCbP0c4
        f Z)  := by
  exact MazurTransfer.order27_certificate_zlTDSq_s0_zlTDCb_s0

#print axioms solution
