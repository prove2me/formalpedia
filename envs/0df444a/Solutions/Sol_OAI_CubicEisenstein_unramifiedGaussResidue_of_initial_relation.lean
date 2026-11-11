-- Prove2me | solution 1 for OAI.CubicEisenstein.unramifiedGaussResidue_of_initial_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:56:24.193206+00:00
-- url     : https://prove2.me/submissions/9b9f10c3-9395-485e-afc4-4a9ce8cb45e3

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimePowerGaussSums
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselDerivatives
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_cuspWhittakerHeightFactor_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_cuspWhittakerHeightFactor_center_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_analyticAt_nonreal
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_opposite_initial
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_residue_limit
import Theorems.Thm_OAI_CubicEisenstein_upperVertical_tendsto_cubic_punctured
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
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_SixthPowerAverage_outsideWeight_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedCoeff_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedMoebius_zero
import Theorems.Thm_OAI_SmoothMobiusCorrection_mem_primeSet
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_succ
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_zero
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.cubicUnitGaussSum_one
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
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
attribute [local simp] OAI.SixthPowerAverage.outsideWeight_zero
attribute [local simp] OAI.SixthPowerAverage.weightedCoeff_zero
attribute [local simp] OAI.SixthPowerAverage.weightedMoebius_zero
attribute [local simp] OAI.SmoothMobiusCorrection.mem_primeSet
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical Topology
open Filter Set
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h0 h1 h2:Eis) (A B:ℂ→ℂ)
    (hA:AnalyticOnNhd ℂ A {s:ℂ|1<s.re ∧ 0<s.im})
    (hB:AnalyticOnNhd ℂ B {s:ℂ|1<s.re ∧ 0<s.im})
    (hAc:ContinuousAt A (4/3:ℂ)) (hBc:ContinuousAt B (4/3:ℂ))
    (hrel:∀s:ℂ,4<s.re→0<s.im→unramifiedCubicGaussSeries s h0=
      A s*unramifiedCubicGaussSeries s h1+B s*unramifiedCubicGaussSeries s h2):
    unramifiedGaussResidue h0=A (4/3)*unramifiedGaussResidue h1+
      B (4/3)*unramifiedGaussResidue h2:=by
  let T (h:Eis):ℂ→ℂ:=translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  let H (h:Eis):ℂ→ℂ:=fun s=>cuspWhittakerHeightFactor s (3*h)
  let D:Set ℂ:={s|1<s.re ∧ 0<s.im}
  let f:ℂ→ℂ:=fun s=>T h0 s*H h1 s*H h2 s
  let g:ℂ→ℂ:=fun s=>A s*T h1 s*H h0 s*H h2 s+B s*T h2 s*H h0 s*H h1 s
  have hT (h:Eis):AnalyticOnNhd ℂ (T h) D:=fun s hs=>
    translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hH (h:Eis):AnalyticOnNhd ℂ (H h) D:=fun s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1
  have hf:AnalyticOnNhd ℂ f D:=fun s hs=>((hT h0 s hs).mul (hH h1 s hs)).mul (hH h2 s hs)
  have hg:AnalyticOnNhd ℂ g D:=fun s hs=>
    (((hA s hs).mul (hT h1 s hs)).mul (hH h0 s hs)).mul (hH h2 s hs) |>.add
      ((((hB s hs).mul (hT h2 s hs)).mul (hH h0 s hs)).mul (hH h1 s hs))
  have hconvex:Convex ℝ D:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hstart:(5+Complex.I:ℂ)∈D:=by norm_num [D]
  have hopen:IsOpen {s:ℂ|4<s.re ∧ 0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:f=ᶠ[𝓝 (5+Complex.I:ℂ)]g:=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g,T,H]
    rw [translatedCuspFamily_opposite_initial h0 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h1 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h2 s hs.1 hs.2,hrel s hs.1 hs.2]
    ring
  have heq:=hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hlimH (h:Eis):Tendsto (H h) (𝓝[≠] (4/3:ℂ)) (𝓝 (H h (4/3))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  let R (h:Eis):ℂ:=translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue
  have hlimT (h:Eis):Tendsto (fun s:ℂ=>(s-4/3)*T h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (R h)):=
    translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  have hl:=(((hlimT h0).mul (hlimH h1)).mul (hlimH h2)).comp upperVertical_tendsto_cubic_punctured
  have hr:=((((hAc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h1)).mul (hlimH h0)).mul
    (hlimH h2) |>.add ((((hBc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h2)).mul
      (hlimH h0)).mul (hlimH h1))).comp upperVertical_tendsto_cubic_punctured
  have hcross:R h0*H h1 (4/3)*H h2 (4/3)=
      A (4/3)*R h1*H h0 (4/3)*H h2 (4/3)+B (4/3)*R h2*H h0 (4/3)*H h1 (4/3):=by
    apply tendsto_nhds_unique_of_eventuallyEq hl hr
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have htD:(4/3:ℂ)+(t:ℂ)*Complex.I∈D:=by
      constructor
      · norm_num
      · simpa using ht
    have hc:=heq htD
    dsimp only [Function.comp_def,f,g] at *
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hc
  change R h0/H h0 (4/3)=A (4/3)*(R h1/H h1 (4/3))+B (4/3)*(R h2/H h2 (4/3))
  have h0ne:H h0 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h0)
  have h1ne:H h1 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h1)
  have h2ne:H h2 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h2)
  field_simp [h0ne,h1ne,h2ne]
  linear_combination hcross
end OAI.CubicEisenstein
