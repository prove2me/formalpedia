-- Prove2me | solution 1 for MazurProof.N13GaussianFieldEquiv.gaussianTheta_root_sextic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:32:40.648689+00:00
-- url     : https://prove2.me/submissions/a7251183-e157-4c9e-9200-a2713af3d5fd

import Mathlib
import Definitions.Def_MazurN13_L3
import Theorems.Thm_MazurProof_N13GaussianGlobalArithmetic_g_mul_conj

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
theorem gaussianTheta_root_n13F :
    eval₂ (algebraMap GI Lg) gaussianTheta
      N13GaussianGlobalArithmetic.n13F = 0 := by
  rw [← N13GaussianGlobalArithmetic.g_mul_conj,
    Polynomial.eval₂_mul, gaussianTheta_root_g, zero_mul]
theorem gaussianTheta_root_sextic :
    eval₂ (algebraMap ℚ Lg) gaussianTheta
      N13SexticSquareclass.f = 0 := by
  simpa [N13SexticSquareclass.f, N13Mumford.f,
    N13GaussianGlobalArithmetic.n13F] using
    gaussianTheta_root_n13F
/-! ## Integrality of the structural generators -/
end
end MazurProof.N13GaussianFieldEquiv
end

end

theorem solution : type_of% @MazurProof.N13GaussianFieldEquiv.gaussianTheta_root_sextic := @MazurProof.N13GaussianFieldEquiv.gaussianTheta_root_sextic
