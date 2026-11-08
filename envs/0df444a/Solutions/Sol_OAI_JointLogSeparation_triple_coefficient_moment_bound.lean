-- Prove2me | solution 1 for OAI.JointLogSeparation.triple_coefficient_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:22.289214+00:00
-- url     : https://prove2.me/submissions/7a44fbb4-2bc9-4e14-91d6-3d5f09ad8b2d

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Theorems.Thm_OAI_JointLogSeparation_weighted_schwartz_integrable
import Theorems.Thm_OAI_JointLogSeparation_density_weight_identity
import Theorems.Thm_OAI_JointLogSeparation_triple_product_integral_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_integrable
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap
open OAI.JointLogSeparation
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FirstPassCubeLabels
namespace OAI.JointLogSeparation
theorem _root_.solution (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖ ≤
      C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * (1 + ‖t₃‖) ^ J *
        ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖) ≤ C * (∫ t : ℝ, firstLogDensity 0 t) ^ 3 := by
  let f₁ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₁ t‖
  let f₂ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₂ t‖
  let f₃ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₃ t‖
  have hprod : ∀ t₁ t₂ t₃ : ℝ,
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * (1 + ‖t₃‖) ^ J *
        ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖ = f₁ t₁ * (f₂ t₂ * f₃ t₃) := by
    intro t₁ t₂ t₃
    simp only [norm_mul, f₁, f₂, f₃]
    ring
  have hb : ∀ t₁ t₂ t₃ : ℝ, S * f₁ t₁ * f₂ t₂ * f₃ t₃ ≤
      C * firstLogDensity 0 t₁ * firstLogDensity 0 t₂ * firstLogDensity 0 t₃ := by
    intro t₁ t₂ t₃
    have h := mul_le_mul_of_nonneg_left (hpoint t₁ t₂ t₃)
      (show 0 ≤ (1 + ‖t₁‖)^J * (1 + ‖t₂‖)^J * (1 + ‖t₃‖)^J by positivity)
    have hd₁ := density_weight_identity J t₁
    have hd₂ := density_weight_identity J t₂
    have hd₃ := density_weight_identity J t₃
    simp only [norm_mul] at h
    rw [← hd₁, ← hd₂, ← hd₃]
    dsimp [f₁, f₂, f₃]
    simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using h
  have hbound := triple_product_integral_bound f₁ f₂ f₃
    (firstLogDensity 0) (firstLogDensity 0) (firstLogDensity 0)
    (weighted_schwartz_integrable b₁ J) (weighted_schwartz_integrable b₂ J)
    (weighted_schwartz_integrable b₃ J)
    (firstLogDensity_integrable 0) (firstLogDensity_integrable 0) (firstLogDensity_integrable 0)
    S C hb
  simp_rw [hprod, integral_const_mul]
  simp_rw [integral_mul_const]
  convert hbound using 1 <;> ring
end OAI.JointLogSeparation
