-- Prove2me | solution 1 for MazurProof.N13GaussianFieldEquiv.gaussianTheta_gaussian_cubic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:26:21.079852+00:00
-- url     : https://prove2.me/submissions/e9729325-d3bc-4755-8237-0d248268204b

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
theorem gaussianTheta_root_g :
    eval₂ (algebraMap GI Lg) gaussianTheta
      N13GaussianGlobalArithmetic.g = 0 := by
  have h := alpha_root_h
  rw [N13GaussianGlobalArithmetic.h,
    Polynomial.eval₂_comp] at h
  simpa only [gaussianTheta, eval₂_add, eval₂_X,
    eval₂_ofNat, map_ofNat] using h
theorem gaussianTheta_gaussian_cubic :
    gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
        gaussianTheta - 1 -
      gaussianI * (2 * gaussianTheta * (gaussianTheta + 1)) = 0 := by
  have hi :
      algebraMap GI Lg N13GaussianGlobalArithmetic.i =
        gaussianI := by
    rw [gaussianI,
      IsScalarTower.algebraMap_apply GI K Lg]
  have hg :
      gaussianTheta ^ 3 +
          (2 - 2 * gaussianI) * gaussianTheta ^ 2 +
          (-1 - 2 * gaussianI) * gaussianTheta - 1 = 0 := by
    simpa [N13GaussianGlobalArithmetic.g, hi,
      map_add, map_sub, map_mul, map_neg, map_one,
      map_ofNat] using gaussianTheta_root_g
  linear_combination hg
/-! ## Integrality of the structural generators -/
end
end MazurProof.N13GaussianFieldEquiv
end

end

theorem solution : type_of% @MazurProof.N13GaussianFieldEquiv.gaussianTheta_gaussian_cubic := @MazurProof.N13GaussianFieldEquiv.gaussianTheta_gaussian_cubic
