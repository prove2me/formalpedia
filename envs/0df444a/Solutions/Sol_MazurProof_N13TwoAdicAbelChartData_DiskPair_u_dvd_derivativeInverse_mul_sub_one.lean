-- Prove2me | solution 1 for MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_derivativeInverse_mul_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:47:11.30581+00:00
-- url     : https://prove2.me/submissions/467a55a8-cb0a-4563-9fa9-55effb2d240f

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData =====
section
/-!
# Integral Mumford data on the nonspecial N13 two-adic Abel chart

A point in the residue disk of `(0,0)` and a point in the residue disk of
`(-1,0)` have distinct `x`-coordinates by a unit.  Lagrange interpolation
therefore gives an integral graph polynomial through the two points.

The product of the two linear factors divides the curve residual.  The same
interpolation argument, applied to the inverses of the two vertical
derivatives, gives the smoothness Bezout identity.  Thus every such pair
defines smooth generalized Mumford data over `ℤ₂`, without a search through
congruence classes.
-/
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
namespace DiskPair
variable (P : DiskPair)
@[simp] theorem derivativeInv₀_mul :
    P.derivativeInv₀ * P.verticalDerivative.eval P.x₀ = 1 := by
  rw [← (P.verticalDerivative_eval_x₀_isUnit).unit_spec]
  exact Units.inv_mul _
@[simp] theorem derivativeInv₁_mul :
    P.derivativeInv₁ * P.verticalDerivative.eval P.x₁ = 1 := by
  rw [← (P.verticalDerivative_eval_x₁_isUnit).unit_spec]
  exact Units.inv_mul _
@[simp] theorem derivativeInverse_mul_eval_x₀ :
    (P.derivativeInverse * P.verticalDerivative).eval P.x₀ = 1 := by
  rw [eval_mul, derivativeInverse, P.interpolate_eval_x₀,
    P.derivativeInv₀_mul]
@[simp] theorem derivativeInverse_mul_eval_x₁ :
    (P.derivativeInverse * P.verticalDerivative).eval P.x₁ = 1 := by
  rw [eval_mul, derivativeInverse, P.interpolate_eval_x₁,
    P.derivativeInv₁_mul]
theorem u_dvd_derivativeInverse_mul_sub_one :
    P.u ∣ P.derivativeInverse * P.verticalDerivative - 1 := by
  have h₀ :
      X - C P.x₀ ∣
        P.derivativeInverse * P.verticalDerivative - 1 := by
    rw [dvd_iff_isRoot, IsRoot]
    rw [eval_sub, P.derivativeInverse_mul_eval_x₀, eval_one,
      sub_self]
  have h₁ :
      X - C P.x₁ ∣
        P.derivativeInverse * P.verticalDerivative - 1 := by
    rw [dvd_iff_isRoot, IsRoot]
    rw [eval_sub, P.derivativeInverse_mul_eval_x₁, eval_one,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      P.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [u, mul_comm] using hprod
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end

end

theorem solution : type_of% @MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_derivativeInverse_mul_sub_one := @MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_derivativeInverse_mul_sub_one
