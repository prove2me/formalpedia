-- Prove2me | solution 1 for MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_curveError
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:45:39.991526+00:00
-- url     : https://prove2.me/submissions/5a180519-2c84-462e-bfae-03cb73e00635

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
@[simp] theorem curveError_eval_x₀ :
    P.curveError.eval P.x₀ = 0 := by
  have hcurve := P.y₀_spec.1
  rw [N13GoodModelTwo.affineEquation_iff_residual] at hcurve
  simpa [curveError, N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using hcurve
@[simp] theorem curveError_eval_x₁ :
    P.curveError.eval P.x₁ = 0 := by
  have hcurve := P.y₁_spec.1
  rw [N13GoodModelTwo.affineEquation_iff_residual] at hcurve
  simpa [curveError, N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using hcurve
theorem u_dvd_curveError :
    P.u ∣ P.curveError := by
  have h₀ : X - C P.x₀ ∣ P.curveError := by
    rw [dvd_iff_isRoot, IsRoot]
    exact P.curveError_eval_x₀
  have h₁ : X - C P.x₁ ∣ P.curveError := by
    rw [dvd_iff_isRoot, IsRoot]
    exact P.curveError_eval_x₁
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      P.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [u, mul_comm] using hprod
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end

end

theorem solution : type_of% @MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_curveError := @MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_curveError
