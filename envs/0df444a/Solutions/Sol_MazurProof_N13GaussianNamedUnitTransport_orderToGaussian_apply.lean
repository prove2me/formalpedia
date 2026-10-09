-- Prove2me | solution 1 for MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:43:32.401216+00:00
-- url     : https://prove2.me/submissions/7b68fadd-0a15-4b4a-99bb-9a1ef9b7e269

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

-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport =====
section
/-!
# Transport of the named N13 units

The unit squareclass computation is carried out in the maximal order of the
Gaussian cubic presentation, while the fake-descent candidates use the sextic
presentation.  This file gives the literal carrier-preserving map between the
two and proves that the three named units agree under it.

Consequently the structural maximal-order unit decomposition transports to the
same three units appearing in `N13CandidateCollapse`, without enumerating the
eight unit squareclasses.
-/
namespace MazurProof.N13GaussianNamedUnitTransport
noncomputable section
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianNamedUnitTransport.fieldLg
/-- The explicit maximal-order map has the same underlying field value as
the canonical ring-of-integers coercion. -/
@[simp] theorem orderToGaussian_apply (x : O) :
    orderToGaussian x = (x : Lg) := by
  letI intAlgebraLg : Algebra ℤ Lg :=
    Ring.toIntAlgebra Lg
  letI hO : IsIntegralClosure O ℤ Lg :=
    NumberField.RingOfIntegers.instIsIntegralClosureInt
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm x :
        N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      (x : Lg)
  simp [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers,
    N13GaussianNumberField.integralClosureToRingOfIntegersRingEquiv,
    N13GaussianNumberField.relativeToAbsoluteAlgEquiv]
  let e :
      (integralClosure ℤ Lg) ≃ₐ[ℤ] O :=
    IsIntegralClosure.equiv
      ℤ (integralClosure ℤ Lg) Lg O
  have he :=
    IsIntegralClosure.algebraMap_equiv
      ℤ (integralClosure ℤ Lg) Lg O (e.symm x)
  calc
    algebraMap (integralClosure ℤ Lg) Lg (e.symm x) =
        algebraMap O Lg (e (e.symm x)) :=
      he.symm
    _ = algebraMap O Lg x := by
      rw [e.apply_symm_apply]
end
end MazurProof.N13GaussianNamedUnitTransport
end

end

theorem solution : type_of% @MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply := @MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
