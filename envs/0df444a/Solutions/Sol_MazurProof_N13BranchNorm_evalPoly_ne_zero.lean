-- Prove2me | solution 1 for MazurProof.N13BranchNorm.evalPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:35:59.609631+00:00
-- url     : https://prove2.me/submissions/73ebf2cb-0e91-40a7-84c6-f57713da99c6

import Mathlib
import Definitions.Def_MazurN13_L0
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_evalAtInfinity_eq_reverse_mul
import Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_eval_parameter_eq_ofPowerSeries

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
omit [CharZero K] in
theorem evalPoly_ne_zero {p : K[X]} (hp : p ≠ 0) :
    evalPoly K p ≠ 0 := by
  rw [evalPoly_eq_evalAtInfinity,
    N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul]
  apply mul_ne_zero
  · rw [N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries]
    intro hzero
    apply hp
    apply Polynomial.reverse_eq_zero.mp
    apply Polynomial.coe_injective K
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using hzero
  · exact pow_ne_zero _
      (inv_ne_zero (N13LaurentPolynomialOrder.parameter_ne_zero K))
end
end MazurProof.N13BranchNorm
end

end

theorem solution : type_of% @MazurProof.N13BranchNorm.evalPoly_ne_zero := @MazurProof.N13BranchNorm.evalPoly_ne_zero
