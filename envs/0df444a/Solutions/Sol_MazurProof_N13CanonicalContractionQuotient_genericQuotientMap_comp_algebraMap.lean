-- Prove2me | solution 1 for MazurProof.N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:03:39.726498+00:00
-- url     : https://prove2.me/submissions/d14e4e5e-ee51-41b1-8025-fc722975c322

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticCoordinateEquiv =====
section
/-!
# Completing the square on the N13 coordinate rings

Over any field of characteristic zero, the good generalized equation

`y² + (X³+X+1)y = X⁵+X⁴`

and the sextic equation already used by the concrete Picard group are
isomorphic by

`Y = 2y + (X³+X+1)`.

This file constructs that isomorphism directly from the two `AdjoinRoot`
presentations and records its action on both coordinates.  It is the
algebraic bridge needed to interpret integral generalized Mumford graph
ideals as classes in the existing oriented sextic Picard group.
-/
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toSextic_algebraMap (z : K) :
    toSextic (K := K)
        (algebraMap K (GoodRing (K := K)) z) =
      algebraMap K (SexticRing (K := K)) z := by
  change
    toSextic (K := K)
        (N13GeneralizedMumfordIntegral.xClass (C z)) =
      SexticMumford.xClass (M (K := K)) (C z)
  exact toSextic_xClass (K := K) (C z)
end
end MazurProof.N13GoodSexticCoordinateEquiv
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralModelContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralModelContraction.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralModelContraction.integralGoodAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization
@[simp] theorem integralToGood_algebraMap
    (a : R₂) :
    integralToGood (algebraMap R₂ IntegralRing a) =
      algebraMap Q₂ GoodRing
        (N13TwoAdicCoordinateBaseChange.coeffMap a) := by
  change
    N13TwoAdicCoordinateBaseChange.extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C a)) =
      N13GeneralizedMumfordIntegral.xClass
        (C (N13TwoAdicCoordinateBaseChange.coeffMap a))
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass]
  simp [N13TwoAdicCoordinateBaseChange.mapPoly,
    N13TwoAdicCoordinateBaseChange.coeffMap]
attribute [local instance] MazurProof.N13IntegralModelContraction.goodRingLocalization
attribute [local instance] MazurProof.N13IntegralModelContraction.integralRationalAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.rationalRingLocalization
end
end MazurProof.N13IntegralModelContraction
end

end

-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13CanonicalContractionQuotient =====
section
/-!
# Generic quotient of a canonical N13 contraction

Extending a canonical vertical contraction to the generic fibre recovers the
original ideal.  The induced map on affine quotients is injective: membership
in the contraction is definitionally membership of the image in the generic
ideal.  For a quadratic Mumford graph, this map carries the literal integral
classes of `1` and `x` to the literal generic quotient basis `{1,x}`.
-/
open Polynomial
namespace MazurProof.N13CanonicalContractionQuotient
noncomputable section
attribute [local instance] MazurProof.N13CanonicalContractionQuotient.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13CanonicalContractionQuotient.integralRationalAlgebra
/-- The generic quotient map respects the two-adic coefficient action. -/
theorem genericQuotientMap_comp_algebraMap
    (J : Ideal RationalRing) :
    (genericQuotientMap J).comp
        (algebraMap R₂
          (IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal J)) =
      algebraMap R₂ (RationalRing ⧸ J) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13TwoAdicCoordinateBaseChange.integralToSextic
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk J (algebraMap R₂ RationalRing r)
  congr 1
  change
    N13GoodSexticCoordinateEquiv.toSextic
        (N13IntegralModelContraction.integralToGood
          (algebraMap R₂ IntegralRing r)) =
      algebraMap R₂ RationalRing r
  rw [N13IntegralModelContraction.integralToGood_algebraMap,
    N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
  exact
    (IsScalarTower.algebraMap_apply R₂ Q₂ RationalRing r).symm
end
end MazurProof.N13CanonicalContractionQuotient
end

end

theorem solution : type_of% @MazurProof.N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap := @MazurProof.N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap
