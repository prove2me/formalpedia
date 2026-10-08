-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSeven_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:07:38.578281+00:00
-- url     : https://prove2.me/submissions/8dca2d86-1ada-4e2b-835e-11c86867f07b

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
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



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert





/-- The discriminant of the parametrized order-seven family. -/
theorem orderSeven_Δ (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, MazurTorsion.Kubert.tateNormalCurve]
  ring





end MazurTorsion.Kubert

end
end MazurTransfer.Order49GeometryEquations

theorem solution (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSeven_Δ <;> assumption
#print axioms solution
