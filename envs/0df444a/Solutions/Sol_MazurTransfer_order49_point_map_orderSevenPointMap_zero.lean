-- Prove2me | solution 1 for MazurTransfer.order49_point_map_orderSevenPointMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:27:17.306345+00:00
-- url     : https://prove2.me/submissions/e239230f-3c50-4e61-b813-56c03ebb4207

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
open Polynomial
namespace MazurTransfer.Order49PointMapHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert


































































































@[simp]
theorem orderSevenPointMap_zero
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenPointMap d 0 = 0 :=
  rfl

































end MazurTorsion.Kubert

end MazurTransfer.Order49PointMapHelpers

theorem solution (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    MazurTorsion.Kubert.orderSevenPointMap d 0 = 0 := by
  apply MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_zero <;> assumption
#print axioms solution
