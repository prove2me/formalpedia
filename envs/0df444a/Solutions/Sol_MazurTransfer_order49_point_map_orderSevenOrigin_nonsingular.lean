-- Prove2me | solution 1 for MazurTransfer.order49_point_map_orderSevenOrigin_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:32:21.50232+00:00
-- url     : https://prove2.me/submissions/9ba112d7-7211-4eab-8ce5-ed732bc76a3f

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib
open Polynomial
namespace MazurTransfer.Order49MarkedOriginNonsingular
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert










































































/-- The marked origin is nonsingular on every nonsingular member of the
order-seven family. -/
theorem orderSevenOrigin_nonsingular
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular 0 0 := by
  apply (MazurTorsion.Kubert.orderSevenFamily d).toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.tateNormalCurve]

























































end MazurTorsion.Kubert

end MazurTransfer.Order49MarkedOriginNonsingular

theorem solution (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular 0 0 := by
  apply MazurTransfer.Order49MarkedOriginNonsingular.MazurTorsion.Kubert.orderSevenOrigin_nonsingular <;> assumption
#print axioms solution
