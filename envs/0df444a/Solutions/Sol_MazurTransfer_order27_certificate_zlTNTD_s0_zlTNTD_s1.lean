-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:27:36.013972+00:00
-- url     : https://prove2.me/submissions/48f1b62e-60e2-47ba-8357-42db5852cfbd

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

lemma zlTNTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z + zlTN1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + zlTNTDP0c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNTDQ0c0 f Z) * hM + (zlTNTDQ0c1 f Z) * hM + (zlTNTDQ0c2 f Z) * hM + (zlTNTDQ0c3 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTN0, zlTN1, zlTNTDP0c0,
      zlTNTDP0c1, zlTNTDP0c2, zlTNTDP0c3, zlTNTDP0c4, zlTNTDQ0c0, zlTNTDQ0c1,
      zlTNTDQ0c2, zlTNTDQ0c3]
  ring1

lemma zlTNTD_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN2 f Z + zlTN3 Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) + (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z)) + zlTNTDP1c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNTDQ1c0 f Z) * hM + (zlTNTDQ1c1 f Z) * hM + (zlTNTDQ1c2 f Z) * hM + (zlTNTDQ1c3 f Z) * hM
      + (zlTNTDQ1c4 f Z) * hM + (zlTNTDQ1c5 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTN2, zlTN3, zlTNTDP1c0,
      zlTNTDP1c1, zlTNTDP1c2, zlTNTDP1c3, zlTNTDP1c4, zlTNTDQ1c0, zlTNTDQ1c1,
      zlTNTDQ1c2, zlTNTDQ1c3, zlTNTDQ1c4, zlTNTDQ1c5]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z + zlTN1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + zlTNTDP0c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN2 f Z + zlTN3 Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) + (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z)) + zlTNTDP1c4
        f Z) := by
  exact ⟨MazurTorsion.Kubert.zlTNTD_s0, MazurTorsion.Kubert.zlTNTD_s1⟩

#print axioms MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN0 f Z + zlTN1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + zlTNTDP0c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN2 f Z + zlTN3 Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) + (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z)) + zlTNTDP1c4
        f Z)  := by
  exact MazurTransfer.order27_certificate_zlTNTD_s0_zlTNTD_s1

#print axioms solution
