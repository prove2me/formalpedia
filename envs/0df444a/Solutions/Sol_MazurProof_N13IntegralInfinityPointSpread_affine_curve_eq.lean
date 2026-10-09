-- Prove2me | solution 1 for MazurProof.N13IntegralInfinityPointSpread.affine_curve_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:56:21.600478+00:00
-- url     : https://prove2.me/submissions/5c76477f-6d62-4f99-ac42-264f44f4a271

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralInfinityPointSpread =====
section
/-!
# Integral point ideals on the N13 infinity chart

An integral point `(t₀,v₀)` on the ordinary infinity chart with
`t₀ ≡ 0 mod 2` defines the linear graph ideal

`(t-t₀, v-v₀)`.

Its generalized Jacobian in the ordinate direction reduces to `1`, hence
is a two-adic unit.  The abstract graph-ideal product theorem then gives an
explicit inverse for this point ideal.  This is the infinity-chart analogue
of the integral affine semigraph construction.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityPointSpread.instFactPrimeOfNatNat_fLT
/-! ## The matching affine-chart closure

On the overlap put `x=t⁻¹` and `y=x³v`.  Clearing these powers from the
infinity graph gives the integral affine graph

`u = 1-t₀x`, `y = v₀x³`.

Its horizontal equation is not monic, but the monicity-free global
Jacobian frame applies.
-/
/-- Weighted homogenization of the infinity point equation gives the exact
affine graph factorization. -/
theorem affine_curve_eq (P : IntegralInfinityPoint) :
    affineV P ^ 2 +
        N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV P -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
      affineU P * affineW P := by
  have hp :
      P.1.2 ^ 2 +
          (1 + P.1.1 ^ 2 + P.1.1 ^ 3) * P.1.2 -
          (P.1.1 + P.1.1 ^ 2) = 0 :=
    sub_eq_zero.mpr P.2
  have hpC :=
    congrArg (Polynomial.C : R₂ →+* R₂[X]) hp
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero] at hpC
  unfold affineU affineV affineW
  simp only [N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly,
    map_sub, map_add, map_mul, map_pow, map_one, map_neg]
  linear_combination X ^ 6 * hpC
end
end MazurProof.N13IntegralInfinityPointSpread
end

end

theorem solution : type_of% @MazurProof.N13IntegralInfinityPointSpread.affine_curve_eq := @MazurProof.N13IntegralInfinityPointSpread.affine_curve_eq
