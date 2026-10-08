-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenVelu_equation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:08:26.656622+00:00
-- url     : https://prove2.me/submissions/b9135bcb-c83a-451b-9c24-ecf297be44e8

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
import Theorems.Thm_MazurTransfer_order49_geometry_equation_iff_completedSquare
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedSquare
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedY
open Polynomial
theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_completedSquare {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x ^ 2 *
        (4 * x ^ 3 + (MazurTorsion.Kubert.orderSevenFamily d).b₂ * x ^ 2 +
          2 * (MazurTorsion.Kubert.orderSevenFamily d).b₄ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).b₆) =
      4 * MazurTorsion.Kubert.orderSevenVeluX d x ^ 3 +
        (MazurTorsion.Kubert.orderSevenQuotient d).b₂ * MazurTorsion.Kubert.orderSevenVeluX d x ^ 2 +
        2 * (MazurTorsion.Kubert.orderSevenQuotient d).b₄ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).b₆ := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_completedSquare <;> assumption

theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_completedY (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_completedY <;> assumption

theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.equation_iff_completedSquare (W : WeierstrassCurve ℚ) (x y : ℚ) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  apply MazurTransfer.order49_geometry_equation_iff_completedSquare <;> assumption
namespace MazurTransfer.Order49GeometryEquations
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert
































































/-- Away from the three kernel abscissae, the explicit Vélu functions
carry the source affine equation to the quotient affine equation. -/
theorem orderSevenVelu_equation
    {d x y : ℚ}
    (hcurve : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Equation x y)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Equation
      (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) := by
  apply (MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.equation_iff_completedSquare
    (MazurTorsion.Kubert.orderSevenQuotient d) (MazurTorsion.Kubert.orderSevenVeluX d x)
      (MazurTorsion.Kubert.orderSevenVeluY d x y)).mpr
  have hsource :=
    (MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.equation_iff_completedSquare (MazurTorsion.Kubert.orderSevenFamily d) x y).mp hcurve
  have hy :
      2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
          (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
        MazurTorsion.Kubert.orderSevenVeluDifferential d x *
          (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
            (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by
    exact MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_completedY d x y
  rw [hy, mul_pow, hsource]
  exact MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_completedSquare hx0 hxb hxc



































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution {d x y : ℚ}
    (hcurve : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Equation x y)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Equation
      (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_equation <;> assumption
#print axioms solution
