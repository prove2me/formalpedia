-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_log_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:00:25.001054+00:00
-- url     : https://prove2.me/submissions/747c0f3b-1a20-4c71-bdd1-894144f7a0ba

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Theorems.Thm_OAI_InitialMeanSquare_sourceRow_nonzero
import Theorems.Thm_OAI_InitialMeanSquare_sourceQuotient_nonzero
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
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
import Theorems.Thm_OAI_SecondPassArithmetic_element_norm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_normLogBin_error
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_primeSubsetGenerator_norm_eq_productNorm
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_SecondPassIntegration_elementNorm_pos
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
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.InitialMeanSquare
theorem _root_.solution (Z : ℝ) (hZ : 0<Z) (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hk : x.frequency≠0) :
    let j := initialLogIndex p x
    let B := elementNorm (secondExpansionQuotient p x)
    let X₀ := initialLogColumn Z B j
    |Real.log (primeProductNorm p x.overlap*X₀/residualScale p Z x)|≤2 ∧
    |Real.log (primeProductNorm p x.divisor/secondLogE j)|≤2 ∧
    |Real.log (primeProductNorm p x.overlap/secondLogV j)|≤2 ∧
    |Real.log (elementNorm (sourceObservation p x).1/secondLogK j)|≤2 := by
  dsimp only
  have he := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hv := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hn : 1≤elementNorm (sourceObservation p x).1 := element_norm_ge_one _ (sourceRow_nonzero p x hk)
  have hrow := normLogBin_error (elementNorm (sourceObservation p x).1) hn
  have hE0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have hV0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne'
  have hB0 := (SecondPassIntegration.elementNorm_pos _ (sourceQuotient_nonzero p hp x hE)).ne'
  have hE1 := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hV1 := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio : primeProductNorm p x.overlap*initialLogColumn Z
      (elementNorm (secondExpansionQuotient p x)) (initialLogIndex p x)/residualScale p Z x=
      (primeProductNorm p x.divisor/normLogScale (normLogBin (primeProductNorm p x.divisor)))*
      (primeProductNorm p x.overlap/normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [initialLogColumn,residualScale,initialLogIndex,secondLogE,secondLogV,
      elementNorm,primeSubsetGenerator_norm_eq_productNorm]
    have hZ0 := hZ.ne'
    dsimp [elementNorm] at hB0
    have hBn : ‖eisEmbedding (secondExpansionQuotient p x)‖≠0 := by
      intro hz
      apply hB0
      rw [hz]
      norm_num
    field_simp [hBn]

  refine ⟨?_,?_,?_,?_⟩
  · rw [hratio,Real.log_mul (div_ne_zero hE0 hE1) (div_ne_zero hV0 hV1),
      abs_of_nonneg (add_nonneg he.1 hv.1)]
    linarith [he.2,hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg he.1]
    linarith [he.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hv.1]
    linarith [hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hrow.1]
    linarith [hrow.2]
end OAI.InitialMeanSquare
