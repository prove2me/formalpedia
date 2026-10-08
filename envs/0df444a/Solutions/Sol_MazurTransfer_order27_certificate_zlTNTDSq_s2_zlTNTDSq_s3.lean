-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:27:38.380963+00:00
-- url     : https://prove2.me/submissions/75d0af0e-0a86-407c-8552-cd8c7f12820e

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

lemma zlTNTDSq_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z) + (zlTNTDSqP2c2 f Z + zlTNTDSqP2c3 f Z)) +
        zlTNTDSqP2c4 f Z := by
  linear_combination (norm := skip)
    (zlTNTDSqQ2c0 f Z) * hM + (zlTNTDSqQ2c1 f Z) * hM + (zlTNTDSqQ2c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP1c0, zlTNTDP1c1,
      zlTNTDSqP2c0, zlTNTDSqP2c1, zlTNTDSqP2c2, zlTNTDSqP2c3, zlTNTDSqP2c4,
      zlTNTDSqQ2c0, zlTNTDSqQ2c1, zlTNTDSqQ2c2]
  ring1

lemma zlTNTDSq_s3 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
        (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z) := by
  linear_combination (norm := skip)
    (zlTNTDSqQ3c0 f Z) * hM + (zlTNTDSqQ3c1 f Z) * hM + (zlTNTDSqQ3c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP1c2, zlTNTDP1c3, zlTNTDP1c4,
      zlTNTDSqP3c0, zlTNTDSqP3c1, zlTNTDSqP3c2, zlTNTDSqP3c3, zlTNTDSqP3c4,
      zlTNTDSqP3c5, zlTNTDSqQ3c0, zlTNTDSqQ3c1, zlTNTDSqQ3c2]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z) + (zlTNTDSqP2c2 f Z + zlTNTDSqP2c3 f Z)) +
        zlTNTDSqP2c4 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP1c2 f Z + zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
        (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z)) := by
  exact ⟨MazurTorsion.Kubert.zlTNTDSq_s2, MazurTorsion.Kubert.zlTNTDSq_s3⟩

#print axioms MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z) + (zlTNTDSqP2c2 f Z + zlTNTDSqP2c3 f Z)) +
        zlTNTDSqP2c4 f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTNTDP1c2 f Z + zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
        (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))  := by
  exact MazurTransfer.order27_certificate_zlTNTDSq_s2_zlTNTDSq_s3

#print axioms solution
