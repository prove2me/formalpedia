-- Prove2me | solution 1 for MazurProof.N13GaussianFieldEquiv.sexticToGaussian_bijective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:44:46.986451+00:00
-- url     : https://prove2.me/submissions/5bf2e244-deda-4517-b57d-6ffba0e51157

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13Mumford_f_monic

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

-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section
/-!
# The Gaussian fraction field as a quadratic number field

The fraction field of `ℤ[i]` has the structural rational basis `(1,i)`.
The only localization point to check is that inverting nonzero ordinary
integers already inverts every nonzero Gaussian integer: `z` divides its
nonzero integer norm `z * star z`.

No embeddings or Gaussian elements are enumerated.
-/
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
namespace MazurProof.N13GaussianFractionField
noncomputable section
open N13GaussianGlobalArithmetic
/-! ## The integral basis `(1,i)` -/
/-! ## Cofinality of ordinary integer denominators -/
/-! ## The localized rational basis -/
theorem finrank_K :
    Module.finrank ℚ K = 2 := by
  rw [Module.finrank_eq_card_basis gaussianBasis]
  simp
/-! ## Power basis, minimal polynomial, and discriminant -/
end
end MazurProof.N13GaussianFractionField
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianFieldEquiv =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFieldEquiv =====
section
/-!
# Equivalence of the sextic and Gaussian-cubic N13 fields

The root `α` of the translated Gaussian cubic gives

`θ = α + 9`.

This file proves that sending the sextic generator to this element is an
isomorphism from the original degree-six algebra to the Gaussian cubic
number field.  Equal absolute dimensions make the injective field map
surjective; no inverse polynomial is searched for.

The intrinsic order-four element of the sextic field maps to the Gaussian
unit `i`.  Consequently the short formulas for the descent generators show
directly that all of them are algebraic integers in the structural absolute
ring of integers.
-/
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLs
attribute [local instance] MazurProof.N13GaussianFieldEquiv.finiteKL
attribute [local instance] MazurProof.N13GaussianFieldEquiv.finiteQL
theorem finrank_Ls :
    Module.finrank ℚ Ls = 6 := by
  change
    Module.finrank ℚ
      (AdjoinRoot N13SexticSquareclass.f) = 6
  rw [(AdjoinRoot.powerBasis
    (by
      simpa [N13SexticSquareclass.f] using
        (N13Mumford.f_monic (K := ℚ)).ne_zero)).finrank]
  simpa [N13SexticSquareclass.f] using
    (N13Mumford.f_natDegree (K := ℚ))
theorem finrank_Lg :
    Module.finrank ℚ Lg = 6 := by
  calc
    Module.finrank ℚ Lg =
        Module.finrank ℚ K * Module.finrank K Lg :=
      (Module.finrank_mul_finrank ℚ K Lg).symm
    _ = 2 * 3 := by
      rw [N13GaussianFractionField.finrank_K]
      congr 1
      rw [Module.finrank_eq_card_basis
        N13GaussianCubicField.powerBasis.basis]
      simp [N13GaussianCubicField.powerBasis_dim]
    _ = 6 := by norm_num
theorem sexticToGaussian_bijective :
    Function.Bijective sexticToGaussian := by
  constructor
  · exact sexticToGaussian.injective
  · apply
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := sexticToGaussian.toLinearMap) ?_).mp
    · exact sexticToGaussian.injective
    · rw [finrank_Ls, finrank_Lg]
/-! ## Integrality of the structural generators -/
end
end MazurProof.N13GaussianFieldEquiv
end

end

theorem solution : type_of% @MazurProof.N13GaussianFieldEquiv.sexticToGaussian_bijective := @MazurProof.N13GaussianFieldEquiv.sexticToGaussian_bijective
