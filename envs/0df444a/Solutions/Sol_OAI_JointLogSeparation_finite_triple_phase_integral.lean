-- Prove2me | solution 1 for OAI.JointLogSeparation.finite_triple_phase_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:31:07.09968+00:00
-- url     : https://prove2.me/submissions/9cc29be3-4ef4-4aec-99fb-4ae53f870337

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_integrable_phase_schwartz
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


attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open OAI.JointLogSeparation
open FourierBridge
namespace OAI.JointLogSeparation
theorem _root_.solution {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (x y z : α → ℝ) (c : α → ℂ) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i))) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ s,
      (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i)) := by
  let f := fun i (t₁ t₂ t₃ : ℝ) =>
    (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i))
  have hi₃ (i : α) (t₁ t₂ : ℝ) : Integrable (f i t₁ t₂) :=
    (((integrable_phase_schwartz b₃ (z i)).mul_const (c i)).const_mul _).const_mul _
  have hi₂ (i : α) (t₁ : ℝ) : Integrable (fun t₂ => ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact ((integrable_phase_schwartz b₂ (y i)).mul_const _).const_mul _
  have hi₁ (i : α) : Integrable (fun t₁ => ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact (integrable_phase_schwartz b₁ (x i)).mul_const _
  change (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) = _
  rw [← integral_finsetSum _ (fun i _ => hi₁ i)]
  apply integral_congr_ae
  filter_upwards [] with t₁
  rw [← integral_finsetSum _ (fun i _ => hi₂ i t₁)]
  apply integral_congr_ae
  filter_upwards [] with t₂
  exact (integral_finsetSum _ (fun i _ => hi₃ i t₁ t₂)).symm
end OAI.JointLogSeparation
