-- Prove2me | solution 1 for MazurTransfer.order49_marked_origin_orderSevenFamily_parameters_ne
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:12:04.269981+00:00
-- url     : https://prove2.me/submissions/efd84d71-8b8b-4247-81b0-babf571bba24

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenFamily_discriminant
open Polynomial
theorem MazurTransfer.Order49MarkedOriginKernelHelpers.MazurTorsion.Kubert.orderSevenFamily_Δ (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  apply MazurTransfer.order49_geometry_orderSevenFamily_discriminant <;> assumption
namespace MazurTransfer.Order49MarkedOriginKernelHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert














































































/-- Nonsingularity excludes the three bad parameters of the order-seven
family. -/
theorem orderSevenFamily_parameters_ne
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  have hsource :
      d ^ 7 * (d - 1) ^ 7 *
          (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ≠ 0 := by
    simpa only [MazurTransfer.Order49MarkedOriginKernelHelpers.MazurTorsion.Kubert.orderSevenFamily_Δ] using
      (MazurTorsion.Kubert.orderSevenFamily d).isUnit_Δ.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    apply hsource
    simp [hd]
  · intro hd
    apply hsource
    simp [hd]
  · intro hK
    apply hsource
    simp [hK]





















































end MazurTorsion.Kubert

end MazurTransfer.Order49MarkedOriginKernelHelpers

theorem solution (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  apply MazurTransfer.Order49MarkedOriginKernelHelpers.MazurTorsion.Kubert.orderSevenFamily_parameters_ne <;> assumption
#print axioms solution
