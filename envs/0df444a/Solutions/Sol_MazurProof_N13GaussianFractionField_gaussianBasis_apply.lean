-- Prove2me | solution 1 for MazurProof.N13GaussianFractionField.gaussianBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:30:54.628994+00:00
-- url     : https://prove2.me/submissions/445152c2-8b66-4d45-823d-4263dbaf76d3

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
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
@[simp] theorem gaussianBasis_apply (j : Fin 2) :
    gaussianBasis j =
      algebraMap GI K (gaussianIntBasis j) :=
  Basis.localizationLocalization_apply
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis j
/-! ## Power basis, minimal polynomial, and discriminant -/
end
end MazurProof.N13GaussianFractionField
end

end

theorem solution : type_of% @MazurProof.N13GaussianFractionField.gaussianBasis_apply := @MazurProof.N13GaussianFractionField.gaussianBasis_apply
