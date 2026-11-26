-- Prove2me | solution 1 for HasSmoothJordanOuterApproximation.homothety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:03.051517+00:00
-- url     : https://prove2.me/submissions/c24481f5-5263-40aa-9deb-4115707a5925

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
import Theorems.Thm_complexMulRealEquiv_apply
import Theorems.Thm_HasSmoothJordanOuterApproximation_similarity
import Theorems.Thm_homothety_apply_eq_const_add_mul
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam
import Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam_deriv
import Theorems.Thm_SmoothJordanDomain_ellipse_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_apply
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_deriv
import Theorems.Thm_SmoothJordanDomain_translate_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.ellipse_boundaryParam
attribute [local simp] SmoothJordanDomain.ellipse_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.ellipse_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.translate_boundaryParam
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_apply
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.translate_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] complexMulRealEquiv_apply

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
namespace HasSmoothJordanOuterApproximation
theorem _root_.solution
    {K : Set ℂ} (hK : HasSmoothJordanOuterApproximation K)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    HasSmoothJordanOuterApproximation (AffineMap.homothety c r '' K) := by
  let d : ℂ := (1 - r) • c
  have hrComplex : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hsim := hK.similarity d (r : ℂ) hrComplex
  convert hsim using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [homothety_apply_eq_const_add_mul]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [homothety_apply_eq_const_add_mul]
end HasSmoothJordanOuterApproximation
