-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstWeightedVolume_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:01:49.968928+00:00
-- url     : https://prove2.me/submissions/e304012f-089c-4e31-82cb-10e9cc6aa69d

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
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
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
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
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinFirstCoefficient_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalDiagonalPowers
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstData_harmonic_sum
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirst_diagonal_scalar
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
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
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U →
      (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,w b*globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  refine ⟨Cd*(Real.exp 1)^3*Cp,by positivity,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hC ht hb1 hb2
  have hB0 : 0<B := by linarith
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have hsum := hcount p hp hinj s B U hB hU hs hC ht hb1 hb2
  change (∑b∈s,θ b)≤_ at hsum
  have hterm (b : GlobalFirstData ι) (hb : b∈s) :
      w b*globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤(Γ*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = w b*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ Γ*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := mul_le_mul_of_nonneg_right (hw b hb).2 (by positivity)
      _ ≤ Γ*(((Real.exp 1)^3*ell*B^2*F)*θ b) := mul_le_mul_of_nonneg_left hsc' hΓ
      _ = _ := by ring
  calc
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*(∑b∈s,θ b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      ring
    _ ≤ (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ = _ := by ring
end OAI.SecondPassArithmetic
