-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenVeluDifferential_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:06:14.801432+00:00
-- url     : https://prove2.me/submissions/8629bc0f-568f-4848-9aa1-b030a2a9c402

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


















































/-- Away from the kernel abscissae, the explicit Vélu differential is the
cleared numerator divided by the cube of the kernel polynomial. -/
theorem orderSevenVeluDifferential_eq_div
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 3 := by
  simp only [MazurTorsion.Kubert.orderSevenVeluDifferential,
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator, MazurTorsion.Kubert.orderSevenKernelPolynomial]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring

















































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 3 := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenVeluDifferential_eq_div <;> assumption
#print axioms solution
