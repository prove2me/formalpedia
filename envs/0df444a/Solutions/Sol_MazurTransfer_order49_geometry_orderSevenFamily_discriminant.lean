-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenFamily_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:08:12.201828+00:00
-- url     : https://prove2.me/submissions/11b55b9b-29ad-44e5-845e-bef9a994920f

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_geometry_orderSeven_discriminant
open Polynomial
theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSeven_Δ (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.order49_geometry_orderSeven_discriminant <;> assumption
namespace MazurTransfer.Order49GeometryEquations
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert









/-- The discriminant of the source order-seven family. -/
theorem orderSevenFamily_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simpa only [MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC] using
    MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSeven_Δ d


























































































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenFamily_Δ <;> assumption
#print axioms solution
