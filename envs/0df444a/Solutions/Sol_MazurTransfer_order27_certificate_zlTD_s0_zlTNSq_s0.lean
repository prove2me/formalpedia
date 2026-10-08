-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTD_s0_zlTNSq_s0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:29.316003+00:00
-- url     : https://prove2.me/submissions/c9c4ab56-13b7-4881-baac-6e1e3f85ae2a

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

lemma zlTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlE0 f Z) * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z := by
  linear_combination (norm := skip)
    (zlTDQ0c0 f Z) * hM
  simp only [kernelCubicM, zlE0, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTDQ0c0]
  ring1

lemma zlTNSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      (zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z) := by
  linear_combination (norm := skip)
    (zlTNSqQ0c0 f Z) * hM + (zlTNSqQ0c1 f Z) * hM + (zlTNSqQ0c2 f Z) * hM + (zlTNSqQ0c3 f Z) * hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNSqP0c0, zlTNSqP0c1, zlTNSqP0c2,
      zlTNSqP0c3, zlTNSqQ0c0, zlTNSqQ0c1, zlTNSqQ0c2, zlTNSqQ0c3]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTD_s0_zlTNSq_s0 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlE0 f Z) * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      (zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) := by
  exact ⟨MazurTorsion.Kubert.zlTD_s0, MazurTorsion.Kubert.zlTNSq_s0⟩

#print axioms MazurTransfer.order27_certificate_zlTD_s0_zlTNSq_s0


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlE0 f Z) * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      (zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z))  := by
  exact MazurTransfer.order27_certificate_zlTD_s0_zlTNSq_s0

#print axioms solution
