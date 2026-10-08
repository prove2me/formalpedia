-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:27:32.979232+00:00
-- url     : https://prove2.me/submissions/d1b038f0-3729-440a-b966-c16eca9bfbd6

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

lemma zlTNSq_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN1 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z)) + zlTNSqP1c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNSqQ1c0 f Z) * hM + (zlTNSqQ1c1 f Z) * hM + (zlTNSqQ1c2 f Z) * hM + (zlTNSqQ1c3 f Z) * hM
      + (zlTNSqQ1c4 f Z) * hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNSqP1c0, zlTNSqP1c1, zlTNSqP1c2,
      zlTNSqP1c3, zlTNSqP1c4, zlTNSqQ1c0, zlTNSqQ1c1, zlTNSqQ1c2, zlTNSqQ1c3,
      zlTNSqQ1c4]
  ring1

lemma zlTNSq_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN2 f Z + zlTN3 Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP2c0 f Z + zlTNSqP2c1 f Z) + (zlTNSqP2c2 f Z + zlTNSqP2c3 f Z)) + zlTNSqP2c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNSqQ2c0 f Z) * hM + (zlTNSqQ2c1 f Z) * hM + (zlTNSqQ2c2 f Z) * hM + (zlTNSqQ2c3 f Z) * hM
      + (zlTNSqQ2c4 f Z) * hM + (zlTNSqQ2c5 f Z) * hM + (zlTNSqQ2c6 f Z) * hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNSqP2c0, zlTNSqP2c1, zlTNSqP2c2,
      zlTNSqP2c3, zlTNSqP2c4, zlTNSqQ2c0, zlTNSqQ2c1, zlTNSqQ2c2, zlTNSqQ2c3,
      zlTNSqQ2c4, zlTNSqQ2c5, zlTNSqQ2c6]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN1 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z)) + zlTNSqP1c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN2 f Z + zlTN3 Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP2c0 f Z + zlTNSqP2c1 f Z) + (zlTNSqP2c2 f Z + zlTNSqP2c3 f Z)) + zlTNSqP2c4
        f Z) := by
  exact ⟨MazurTorsion.Kubert.zlTNSq_s1, MazurTorsion.Kubert.zlTNSq_s2⟩

#print axioms MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN1 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z)) + zlTNSqP1c4
        f Z)
  ∧ (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTN2 f Z + zlTN3 Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP2c0 f Z + zlTNSqP2c1 f Z) + (zlTNSqP2c2 f Z + zlTNSqP2c3 f Z)) + zlTNSqP2c4
        f Z)  := by
  exact MazurTransfer.order27_certificate_zlTNSq_s1_zlTNSq_s2

#print axioms solution
