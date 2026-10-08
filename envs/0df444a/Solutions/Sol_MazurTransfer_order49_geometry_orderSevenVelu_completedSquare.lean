-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenVelu_completedSquare
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:07:21.230195+00:00
-- url     : https://prove2.me/submissions/f3dafab1-662f-4afc-99da-2d1bb266e46c

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
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVeluDifferential_eq_div
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVeluX_eq_div
open Polynomial
theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 3 := by
  apply MazurTransfer.order49_geometry_orderSevenVeluDifferential_eq_div <;> assumption

theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVeluX_eq_div {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluX d x =
      MazurTorsion.Kubert.orderSevenVeluXNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2 := by
  apply MazurTransfer.order49_geometry_orderSevenVeluX_eq_div <;> assumption
namespace MazurTransfer.Order49GeometryEquations
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert




























































/-- The completed-square cubic identity behind the explicit Vélu map. -/
theorem orderSevenVelu_completedSquare
    {d x : ℚ} (hx0 : x ≠ 0)
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
  rw [MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div hx0 hxb hxc,
    MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVeluX_eq_div hx0 hxb hxc]
  have hkernel : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  field_simp [hkernel]
  simp only [MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator,
    MazurTorsion.Kubert.orderSevenVeluXNumerator,
    MazurTorsion.Kubert.orderSevenKernelPolynomial,
    MazurTorsion.Kubert.orderSevenFamily,
    MazurTorsion.Kubert.tateNormalCurve, MazurTorsion.Kubert.orderSevenQuotient, MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring







































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution {d x : ℚ} (hx0 : x ≠ 0)
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
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVelu_completedSquare <;> assumption
#print axioms solution
