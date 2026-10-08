-- Prove2me | solution 1 for MazurTransfer.order27_certificate_zlTDCb_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:26:35.786818+00:00
-- url     : https://prove2.me/submissions/b697ba2d-6454-4f50-ae7e-df19716fa3b3

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

lemma zlTDCb_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z + zlTDSqP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTDCbP1c0 f Z + zlTDCbP1c1 f Z) + (zlTDCbP1c2 f Z + zlTDCbP1c3 f Z)) +
        (zlTDCbP1c4 f Z + zlTDCbP1c5 f Z) := by
  linear_combination (norm := skip)
    (zlTDCbQ1c0 f Z) * hM + (zlTDCbQ1c1 f Z) * hM + (zlTDCbQ1c2 f Z) * hM
  simp only [kernelCubicM, zlTDCbP1c0, zlTDCbP1c1, zlTDCbP1c2, zlTDCbP1c3, zlTDCbP1c4,
      zlTDCbP1c5, zlTDCbQ1c0, zlTDCbQ1c1, zlTDCbQ1c2, zlTDP0c0, zlTDP0c1, zlTDP0c2,
      zlTDSqP0c2, zlTDSqP0c3, zlTDSqP0c4]
  ring1

end MazurTorsion.Kubert

theorem MazurTransfer.order27_certificate_zlTDCb_s1 :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDSqP0c2 f Z + zlTDSqP0c3 f Z + zlTDSqP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTDCbP1c0 f Z + zlTDCbP1c1 f Z) + (zlTDCbP1c2 f Z + zlTDCbP1c3 f Z)) +
        (zlTDCbP1c4 f Z + zlTDCbP1c5 f Z)) := by
  exact MazurTorsion.Kubert.zlTDCb_s1

#print axioms MazurTransfer.order27_certificate_zlTDCb_s1


theorem solution :
  (∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(zlTDSqP0c2 f Z + zlTDSqP0c3 f Z + zlTDSqP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTDCbP1c0 f Z + zlTDCbP1c1 f Z) + (zlTDCbP1c2 f Z + zlTDCbP1c3 f Z)) +
        (zlTDCbP1c4 f Z + zlTDCbP1c5 f Z))  := by
  exact MazurTransfer.order27_certificate_zlTDCb_s1

#print axioms solution
