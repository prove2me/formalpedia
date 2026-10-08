-- Prove2me | solution 1 for MazurTransfer.order49_geometry_orderSevenQuotient_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:08:55.31218+00:00
-- url     : https://prove2.me/submissions/7170deea-3b93-4564-b9a2-4e324cbf03a4

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
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenFamily_discriminant
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenQuotient_discriminant
open Polynomial
theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenFamily_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.order49_geometry_orderSevenFamily_discriminant <;> assumption

theorem MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenQuotient_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      d * (d - 1) * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ^ 7 := by
  apply MazurTransfer.order49_geometry_orderSevenQuotient_discriminant <;> assumption
namespace MazurTransfer.Order49GeometryEquations
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert



















/-- Nonsingularity of the source family implies nonsingularity of its
explicit order-seven quotient model. -/
public noncomputable instance orderSevenQuotient_isElliptic
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenQuotient d).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
    MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenQuotient_Δ]
  have hsource :
      d ^ 7 * (d - 1) ^ 7 *
          (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ≠ 0 := by
    simpa only [MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenFamily_Δ] using
      (MazurTorsion.Kubert.orderSevenFamily d).isUnit_Δ.ne_zero
  have hd0 : d ≠ 0 := by
    intro hd
    apply hsource
    simp [hd]
  have hd1 : d ≠ 1 := by
    intro hd
    apply hsource
    simp [hd]
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hK
    apply hsource
    simp [hK]
  exact mul_ne_zero (mul_ne_zero hd0 (sub_ne_zero.mpr hd1))
    (pow_ne_zero 7 hK)
















































































































end MazurTorsion.Kubert

end MazurTransfer.Order49GeometryEquations

theorem solution (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenQuotient d).IsElliptic := by
  apply MazurTransfer.Order49GeometryEquations.MazurTorsion.Kubert.orderSevenQuotient_isElliptic <;> assumption
#print axioms solution
