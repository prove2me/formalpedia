-- Prove2me | solution 1 for MazurTransfer.order49_geometry_equation_iff_completedSquare
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:07:43.968222+00:00
-- url     : https://prove2.me/submissions/4b80fd9b-1f16-4e2c-93ff-ea8fab2089f4

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






























































private theorem equation_iff_completedSquare
    (W : WeierstrassCurve ℚ) (x y : ℚ) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  constructor <;> intro h
  · linear_combination 4 * h
  · linear_combination (1 / 4 : ℚ) * h





































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution (W : WeierstrassCurve ℚ) (x y : ℚ) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.equation_iff_completedSquare <;> assumption
#print axioms solution
