-- Prove2me | solution 1 for MazurProof.N13GoodCoordinateRingTwo.yClass_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:33.925883+00:00
-- url     : https://prove2.me/submissions/f1b35bac-9f03-4a0e-a386-0f44f72fd2ae

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem yClass_relation :
    yClass ^ 2 + xClass hPoly * yClass = xClass rhsPoly := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodCoordinateRingTwo.yClass_relation := @MazurProof.N13GoodCoordinateRingTwo.yClass_relation
