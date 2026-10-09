-- Prove2me | solution 1 for MazurProof.N13GaussianGlobalReductionTwo.shiftedTheta_root_h
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:50:39.294974+00:00
-- url     : https://prove2.me/submissions/8d78b019-40bc-4856-8031-100e3f62b291

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GaussianOrderTwo_i_sq

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

-- ===== FLT.Assumptions.MazurProof.N13GaussianOrderTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianOrderTwo =====
section
/-!
# The fixed Gaussian order at two for N13

This file constructs the first ramified quotient directly from the
Gaussian cubic presentation.  We first adjoin a root `i` of `T² + 1`
over `ℤ₂`, and then a root `θ` of

`T³ + 2T² - T - 1 - i(2T(T+1))`.

Sending `i` to `1 + ε` and `θ` to the cubic residue `α` defines a
surjective ring homomorphism to `𝔽₈[ε]/(ε²)`.  Its kernel is proved to
be exactly `(1-i)² = (2)` by the two nested monic power bases.  Hence the
ramified-prime-square quotient is identified with the dual-number ring.
This is the direct quotient-ring core needed by the local N13 descent;
no ray-class enumeration is involved.

The remaining arithmetic identification with the completed maximal
order is recorded separately in `scratch/N13_GAUSSIAN_ORDER_TWO.md`.
-/
open Polynomial
open scoped CharTwo
namespace MazurProof.N13GaussianOrderTwo
noncomputable section
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module
/-! ## The integral Gaussian cubic order -/
theorem theta_gaussian_cubic :
    theta ^ 3 + 2 * theta ^ 2 - theta - 1 -
      i * (2 * theta * (theta + 1)) = 0 := by
  have h :
      AdjoinRoot.mk cubicPolynomial cubicPolynomial = 0 :=
    AdjoinRoot.mk_self
  change
    (AdjoinRoot.mk cubicPolynomial X) ^ 3 +
          2 * (AdjoinRoot.mk cubicPolynomial X) ^ 2 -
        AdjoinRoot.mk cubicPolynomial X - 1 -
      AdjoinRoot.mk cubicPolynomial (C gaussianI) *
        (2 * AdjoinRoot.mk cubicPolynomial X *
          (AdjoinRoot.mk cubicPolynomial X + 1)) = 0 at h
  exact h
/-! ## The two nested power bases -/
/-! ## Direct reduction to the dual-number ring -/
/-! ## Exactness of the first-jet quotient -/
/-! ## Compatibility with the N13 descent generators -/
/-! ## The ramified prime square -/
/-! ## Structural surjectivity -/
end
end MazurProof.N13GaussianOrderTwo
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalReductionTwo =====
section
/-!
# Global N13 integers in the first ramified quotient at two

The relative maximal order is monogenic over the Gaussian integers.  Its
power-basis universal property therefore maps the full global maximal order
to the fixed integral Gaussian order used at two:

* the Gaussian generator maps to the local generator `i`;
* the translated cubic generator maps to `theta - 9`.

Composing with the exact quotient map gives a genuine ring homomorphism from
the full ring of integers to `F₈[ε]/(ε²)`.  Thus later logarithmic detectors
act on every global unit, rather than only on a displayed list of elements.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalReductionTwo
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraL
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraRelativeO
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraAbsoluteO
@[simp] theorem giToOrder_i :
    giToOrder N13GaussianGlobalArithmetic.i =
      N13GaussianOrderTwo.i := by
  simp [giToOrder, N13GaussianGlobalArithmetic.i]
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder
@[simp] theorem algebraMap_gi_i :
    algebraMap GI Order N13GaussianGlobalArithmetic.i =
      N13GaussianOrderTwo.i :=
  giToOrder_i
theorem shiftedTheta_root_h :
    aeval
        (N13GaussianOrderTwo.theta - 9 : Order)
        N13GaussianGlobalArithmetic.h = 0 := by
  rw [N13GaussianGlobalArithmetic.h, aeval_def,
    eval₂_comp]
  have hinner :
      eval₂ (algebraMap GI Order)
          (N13GaussianOrderTwo.theta - 9)
          (X + C 9) =
        N13GaussianOrderTwo.theta := by
    simp only [eval₂_add, eval₂_X, eval₂_C]
    change
      N13GaussianOrderTwo.theta - 9 +
          giToOrder (9 : GI) =
        N13GaussianOrderTwo.theta
    simp [giToOrder]
  rw [hinner]
  simp only [N13GaussianGlobalArithmetic.g,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, eval₂_one, eval₂_ofNat,
    eval₂_neg, map_ofNat, map_one, map_neg, map_sub, map_mul,
    algebraMap_gi_i]
  linear_combination
    N13GaussianOrderTwo.theta_gaussian_cubic
end
end MazurProof.N13GaussianGlobalReductionTwo
end

end

theorem solution : type_of% @MazurProof.N13GaussianGlobalReductionTwo.shiftedTheta_root_h := @MazurProof.N13GaussianGlobalReductionTwo.shiftedTheta_root_h
