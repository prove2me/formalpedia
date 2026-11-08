-- Prove2me | solution 1 for OAI.JointLogSeparation.triple_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:13:59.11368+00:00
-- url     : https://prove2.me/submissions/d697391b-47c4-43f7-a582-442f64417776

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ChildTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_IntegratedTransfer
import Theorems.Thm_OAI_JointLogSeparation_tripleCoefficient_bounded_integrable
import Theorems.Thm_OAI_JointLogSeparation_tripleCoefficient_norm_bounded_integrable
import Theorems.Thm_OAI_JointLogSeparation_tripleCoefficient_slice_integrable
import Theorems.Thm_OAI_JointLogSeparation_tripleCoefficient_norm_slice_integrable
import Theorems.Thm_OAI_JointLogSeparation_nested_eq_integral
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
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
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
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
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
open scoped BigOperators
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.JointLogSeparation
namespace OAI.JointLogSeparation
theorem _root_.solution (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (G : Frequency → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (D M : ℝ) (hD : 0 ≤ D) (hM : ∀ t, G t ≤ M)
    (hpoint : ∀ t, ‖F t‖ ≤ D * G t) :
    ‖∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F (t₁,t₂,t₃)‖ ≤
    D * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) := by
  have hFb : ∀ t, ‖F t‖ ≤ D * M := fun t => (hpoint t).trans (mul_le_mul_of_nonneg_left (hM t) hD)
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by simpa [Real.norm_of_nonneg (hG0 t)] using hM t
  have hfi := tripleCoefficient_bounded_integrable b₁ b₂ b₃ F hF (D*M) hFb
  have hgi := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  rw [nested_eq_integral _ hfi (tripleCoefficient_slice_integrable b₁ b₂ b₃ F hF (D*M) hFb),
    nested_eq_integral _ hgi (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb)]
  calc
    _ ≤ ∫ t : Frequency, ‖tripleCoefficient b₁ b₂ b₃ t * F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Frequency, D * (‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) := by
      apply integral_mono hfi.norm (hgi.const_mul D)
      intro t
      simp only [norm_mul]
      calc
        _ ≤ ‖tripleCoefficient b₁ b₂ b₃ t‖ * (D * G t) :=
          mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _
end OAI.JointLogSeparation
