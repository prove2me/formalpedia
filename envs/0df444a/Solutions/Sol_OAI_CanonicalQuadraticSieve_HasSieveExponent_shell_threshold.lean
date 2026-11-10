-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.shell_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:46:57.960652+00:00
-- url     : https://prove2.me/submissions/ee3e037d-0276-443b-a960-85d0cb6832e2

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_ball_selected_high
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_low_threshold
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_small_columns
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_fixedCutoffBase_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_selectedPoisson_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_large_rows
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FiniteSieveOperator_energy_bound
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
import Theorems.Thm_OAI_QuadraticInitialBound_initialSieveConstant_pos
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) :
    ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^(2-1/α)≤M →
      ∀a : idealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a≤C*(M*N)^ρ*M*∑J,‖a J‖^2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : η≤ρ/600 := min_le_right _ _
  have h6 : 6*η≤ρ := by linarith only [hηρ,hη]
  have h260 : 260*η≤ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  let C := 790*I+CL+CH
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1≤M*N := by nlinarith only [hM,hN]
  have hPρ : 1≤(M*N)^ρ := Real.one_le_rpow hP hρ.le
  have hE : 0≤∑J,‖a J‖^2 := by positivity
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x≤y) :
      x*M*∑J,‖a J‖^2 ≤ y*M*∑J,‖a J‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a≤sieveNorm M N*∑J,‖a J‖^2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N^2≤M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N≤28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M≤N^2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N)^(6*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N)^(260*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := hb
    _ ≤ (CL*(M*N)^(6*η)*M+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N)^ρ*M+CH*(M*N)^ρ*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N)^ρ*M*∑J,‖a J‖^2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH≤C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
