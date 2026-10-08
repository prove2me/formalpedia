-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenVelu_completedY
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:07:29.65189+00:00
-- url     : https://prove2.me/submissions/4f0a657b-22b2-47fa-b9ac-fec3ceebc113

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open Polynomial
namespace MazurTransfer.Order49GeometryEquations
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert






































/-- The completed ordinate of the Vélu image is the source completed
ordinate multiplied by the explicit differential factor. -/
theorem orderSevenVelu_completedY (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
  simp only [MazurTorsion.Kubert.orderSevenVeluY, MazurTorsion.Kubert.orderSevenQuotient,
    MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.tateNormalCurve]
  ring





























































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_completedY <;> assumption
#print axioms solution
