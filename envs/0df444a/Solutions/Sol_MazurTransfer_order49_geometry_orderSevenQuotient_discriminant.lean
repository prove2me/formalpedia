-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenQuotient_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:08:18.023977+00:00
-- url     : https://prove2.me/submissions/3d832bde-2b56-480f-b6eb-e0734c43ed2b

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
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











/-- The discriminant of the marked order-seven quotient model. -/
theorem orderSevenQuotient_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      d * (d - 1) * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ^ 7 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, MazurTorsion.Kubert.orderSevenQuotient,
    MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring
























































































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      d * (d - 1) * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ^ 7 := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenQuotient_Δ <;> assumption
#print axioms solution
