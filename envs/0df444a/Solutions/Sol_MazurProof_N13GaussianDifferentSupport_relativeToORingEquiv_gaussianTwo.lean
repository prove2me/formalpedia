-- Prove2me | solution 1 for MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:31:35.249573+00:00
-- url     : https://prove2.me/submissions/a97ccc13-d506-4198-9bd8-f95e280486a1

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

-- ===== FLT.Assumptions.MazurProof.N13GaussianDifferentSupport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianDifferentSupport =====
section
/-!
# Structural support of the N13 derivative

The two exceptional Gaussian factors are kept as literal algebraic
integers in the absolute maximal order:

* `A = 1 - i θ² - (1 + i) θ`,
* `Q = 2 - 3i`.

The Gaussian cubic relation gives the two short identities

`f'(θ) = 4 · i θ² (θ + 1) · A²`

and

`13 = (i - θ) · A³ · Q`.

All factors omitted from these displayed powers are exhibited as units.
Thus the different support and the ramification indices are read from
factorizations in the maximal order, rather than from a factor table or a
finite residue-field enumeration.
-/
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianDifferentSupport
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.numberFieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fractionRingOL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.intAlgebraO
/-! ## Norms and the ramified prime -/
/-! ## The residue-degree-three prime

Primality of `Q` is not inferred from its composite norm.  Instead we
descend to the Gaussian prime `(2-3i)`.  The relative cubic is irreducible
there: in the thirteen-element residue field, Frobenius and a quadratic
Bézout identity exclude roots. -/
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindRelativeO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeGIL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeRelativeO
/-! ## The unique prime above two -/
@[simp] theorem relativeToORingEquiv_gaussianTwo :
    relativeToORingEquiv
        (algebraMap GI RelativeO gaussianTwoInteger) =
      primeTwoInteger := by
  apply Subtype.ext
  change
    algebraMap GI L gaussianTwoInteger =
      1 - gaussianI
  simp [gaussianTwoInteger,
    N13GaussianGlobalArithmetic.i,
    N13GaussianFieldEquiv.gaussianI,
    IsScalarTower.algebraMap_apply GI K L]
/-! ## Height-one carriers and support of the different -/
open IsDedekindDomain
/-! ## Square norm and the two remaining parity bits -/
end
end MazurProof.N13GaussianDifferentSupport
end

end

theorem solution : type_of% @MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo := @MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
