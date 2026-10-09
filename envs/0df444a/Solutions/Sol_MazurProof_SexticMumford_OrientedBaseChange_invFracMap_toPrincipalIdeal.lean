-- Prove2me | solution 1 for MazurProof.SexticMumford.OrientedBaseChange.invFracMap_toPrincipalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:22:41.726094+00:00
-- url     : https://prove2.me/submissions/77818ed6-4450-403e-9fde-b5d01a77b441

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_nonZeroDivisors_le_comap

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
/-!
# Base change of oriented Picard classes for smooth sextics

An injective coefficient map carrying one sextic equation to another induces
maps on the affine coordinate rings, their fraction fields, and invertible
fractional ideals.  If the distinguished infinity orders are compatible,
the resulting map on oriented fractional ideals descends to an additive map
of the concrete oriented Picard groups.

The construction is algebraic: extension of fractional ideals and a quotient
universal property.  It does not use a relative Picard scheme.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem invFracMap_toPrincipalIdeal
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (α : (FunctionField M)ˣ) :
    invFracMap ι hι hM
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α) =
      toPrincipalIdeal (CoordinateRing M') (FunctionField M')
        (functionUnitMap ι hι hM α) := by
  apply Units.ext
  simp only [invFracMap, functionUnitMap, Units.coe_map,
    coe_toPrincipalIdeal]
  change
    fractionalMap ι hι hM
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (α : FunctionField M)) =
      FractionalIdeal.spanSingleton (CoordinateRing M')⁰
        (functionMap ι hι hM (α : FunctionField M))
  rw [fractionalMap, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_spanSingleton]
  rfl
end
end MazurProof.SexticMumford.OrientedBaseChange
end

end

theorem solution : type_of% @MazurProof.SexticMumford.OrientedBaseChange.invFracMap_toPrincipalIdeal := @MazurProof.SexticMumford.OrientedBaseChange.invFracMap_toPrincipalIdeal
