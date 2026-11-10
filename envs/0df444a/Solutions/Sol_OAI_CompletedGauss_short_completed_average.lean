-- Prove2me | solution 1 for OAI.CompletedGauss.short_completed_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:46:04.214102+00:00
-- url     : https://prove2.me/submissions/b991caaa-ca34-45a2-b738-d8e06f046341

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CompletedGauss_short_cube_scales
import Theorems.Thm_OAI_CompletedGauss_short_completed_branch
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_DescentFiberCost_finite_ideal_count_real
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
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
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
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace OAI.CompletedGauss
theorem _root_.solution {κ : Type*} [Fintype κ]
    (Z K R X F A : ℝ) (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (Ψ : idealRange F → κ → O →* ℂ) (hΨ : ∀f k z,‖Ψ f k z‖≤1) (W : ℝ → ℂ)
    (hcompleted : ∀f : idealRange F, ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ f k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)/F≤
      256*A*K*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by
  have hZ0 : 0<Z := by linarith
  have hh : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hx := (short_cube_scales Z K R X F 1 hZ hK hR hF hFZ le_rfl hh hmargin).1
  norm_num at hx
  have hX : 0<X := by linarith
  let B := (256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2
  have hb (f : idealRange F) :
      (∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)≤2*A*K*B := by
    apply short_completed_branch (Ψ f) (hΨ f) W Z K R X F A hZ hK hR hF hFZ hA hmargin
    intro H hH
    apply (hcompleted f H hH).trans
    gcongr
    exact (mem_idealRange.mp f.property).2
  have hc : ((idealRange F).card:ℝ)≤128*F := by
    apply DescentFiberCost.finite_ideal_count_real _ _ hF
    · intro I hI
      exact (mem_idealRange.mp hI).1.1
    · intro I hI
      exact (mem_idealRange.mp hI).2
  have hsum : (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)≤
      (128*F)*(2*A*K*B) := by
    calc
      _ ≤ ∑_f : idealRange F,2*A*K*B := Finset.sum_le_sum (fun f _ => hb f)
      _ = ((idealRange F).card:ℝ)*(2*A*K*B) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by dsimp [B]; positivity)
  change _≤256*A*K*B
  calc
    _ ≤ ((128*F)*(2*A*K*B))/F := div_le_div_of_nonneg_right hsum (by linarith)
    _ = _ := by field_simp; ring
end OAI.CompletedGauss
