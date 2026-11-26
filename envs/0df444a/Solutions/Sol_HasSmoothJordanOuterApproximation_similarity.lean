-- Prove2me | solution 1 for HasSmoothJordanOuterApproximation.similarity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:37.711768+00:00
-- url     : https://prove2.me/submissions/d6ac3c8b-1bde-484a-a3fe-bb1f989b6624

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
import Theorems.Thm_complexMulRealEquiv_apply
import Theorems.Thm_closure_translate_linearImage_complexMulRealEquiv
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
    (c a : ℂ) (ha : a ≠ 0) :
    HasSmoothJordanOuterApproximation ((fun z => c + a * z) '' K) := by
  intro ε hε
  let δ : ℝ := ε / ‖a‖
  have haNorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hδ : 0 < δ := by
    exact div_pos hε haNorm
  obtain ⟨Omega, hKOmega, hOmegaK⟩ := hK δ hδ
  let Psi : SmoothJordanDomain :=
    (Omega.linearImage (complexMulRealEquiv a ha)).translate c
  refine ⟨Psi, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨a * z, ⟨z, hKOmega hz, rfl⟩, rfl⟩
  · rw [show closure Psi.carrier =
        (fun z => c + a * z) '' closure Omega.carrier by
      exact closure_translate_linearImage_complexMulRealEquiv Omega c a ha]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hwK, hzw⟩ :=
      Metric.mem_thickening_iff.mp (hOmegaK hz)
    refine Metric.mem_thickening_iff.mpr
      ⟨c + a * w, ⟨w, hwK, rfl⟩, ?_⟩
    have hscale : ‖a‖ * δ = ε := by
      dsimp only [δ]
      exact mul_div_cancel₀ ε haNorm.ne'
    rw [dist_add_left]
    change dist (a • z) (a • w) < ε
    rw [dist_smul₀]
    calc
      ‖a‖ * dist z w < ‖a‖ * δ := mul_lt_mul_of_pos_left hzw haNorm
      _ = ε := hscale
end HasSmoothJordanOuterApproximation
