-- Prove2me | solution 1 for OAI.CubicEisenstein.finite_unramified_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:16:51.796806+00:00
-- url     : https://prove2.me/submissions/713f5971-1035-4e2e-aca0-448d12c31bed

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution {ι:Type*} [Fintype ι] [DecidableEq ι]
    (index:ι→Eis) (coefficient:ι→ℂ→ℂ)
    (hc:∀i s,1<s.re→AnalyticAt ℂ (coefficient i) s)
    (f:ℂ→ℂ) (R:ℂ)
    (hf:∀s,1<s.re→0<s.im→AnalyticAt ℂ f s)
    (hlim:Tendsto (fun s:ℂ=>(s-4/3)*f s) (𝓝[≠] (4/3:ℂ)) (𝓝 R))
    (hinit:∀s:ℂ,4<s.re→0<s.im→
      f s=∑i,coefficient i s*unramifiedCubicGaussSeries s (index i)) :
    R=∑i,coefficient i (4/3)*unramifiedGaussResidue (index i) := by
  let H:ι→ℂ→ℂ:=fun i s=>cuspWhittakerHeightFactor s (3*index i)
  let G:ι→ℂ→ℂ:=fun i s=>translatedCuspFamily (3*index i) oppositeSource 2 3
    (by norm_num) (by norm_num) s
  let D:ℂ→ℂ:=fun s=>∏i,H i s
  let E:ι→ℂ→ℂ:=fun i s=>∏j∈Finset.univ.erase i,H j s
  have hH:∀i s,1<s.re→AnalyticAt ℂ (H i) s:=fun i s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*index i) s hs
  have hD:∀s,1<s.re→AnalyticAt ℂ D s:=fun s hs=>
    Finset.analyticAt_fun_prod _ (fun i hi=>hH i s hs)
  have hE:∀i s,1<s.re→AnalyticAt ℂ (E i) s:=fun i s hs=>
    Finset.analyticAt_fun_prod _ (fun j hj=>hH j s hs)
  have hprod (i:ι) (s:ℂ):H i s*E i s=D s:=by
    exact Finset.mul_prod_erase Finset.univ (fun j=>H j s) (Finset.mem_univ i)
  let domain:Set ℂ:={s|1<s.re∧0<s.im}
  have hconvex:Convex ℝ domain:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have ha:AnalyticOnNhd ℂ (fun s=>f s*D s) domain:=fun s hs=>(hf s hs.1 hs.2).mul (hD s hs.1)
  have hb:AnalyticOnNhd ℂ (fun s=>∑i,coefficient i s*G i s*E i s) domain:=by
    intro s hs
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact ((hc i s hs.1).mul (translatedCuspFamily_analyticAt_nonreal (3*index i)
      oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')).mul (hE i s hs.1)
  have hopen:IsOpen {s:ℂ|4<s.re∧0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:(fun s=>f s*D s)=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>∑i,coefficient i s*G i s*E i s):=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [hinit s hs.1 hs.2,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    rw [translatedCuspFamily_opposite_initial (index i) s hs.1 hs.2]
    change coefficient i s*unramifiedCubicGaussSeries s (index i)*D s=
      coefficient i s*(unramifiedCubicGaussSeries s (index i)*H i s)*E i s
    rw [←hprod i s]
    ring
  have heq:=ha.eqOn_of_preconnected_of_eventuallyEq hb hconvex.isPreconnected
    (show (5+Complex.I:ℂ)∈domain by norm_num [domain]) hev
  have hDc:Tendsto D (𝓝[≠] (4/3:ℂ)) (𝓝 (D (4/3))):=
    (hD (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl:=(hlim.mul hDc).comp upperVertical_tendsto_cubic_punctured
  have hg:∀i,Tendsto (fun s:ℂ=>coefficient i s*((s-4/3)*G i s)*E i s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
        cubicEisensteinResidue*E i (4/3))):=by
    intro i
    exact (((hc i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (translatedCuspFamily_residue_limit (3*index i) oppositeSource 2 3
        (by norm_num) (by norm_num))).mul
          ((hE i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hr:=(tendsto_finsetSum Finset.univ (fun i hi=>hg i)).comp upperVertical_tendsto_cubic_punctured
  have hel:(fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*f ((4/3:ℂ)+(t:ℂ)*Complex.I))*
      D ((4/3:ℂ)+(t:ℂ)*Complex.I))=ᶠ[𝓝[>] (0:ℝ)]
      (fun t:ℝ=>∑i,coefficient i ((4/3:ℂ)+(t:ℂ)*Complex.I)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*G i ((4/3:ℂ)+(t:ℂ)*Complex.I))*
          E i ((4/3:ℂ)+(t:ℂ)*Complex.I)):=by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0:0<t:=ht
    have he:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
      constructor
      · norm_num
      · simpa using ht0)
    dsimp only at he
    rw [mul_assoc,he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hres:=tendsto_nhds_unique_of_eventuallyEq hl hr hel
  have hDn:D (4/3)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>
    cuspWhittakerHeightFactor_center_ne_zero (3*index i))
  apply mul_right_cancel₀ hDn
  rw [Finset.sum_mul]
  refine hres.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  change coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
    cubicEisensteinResidue*E i (4/3)=coefficient i (4/3)*
      (translatedCuspFourier (3*index i) oppositeSource cubicEisensteinResidue/H i (4/3))*D (4/3)
  rw [←hprod i (4/3)]
  field_simp [show H i (4/3)≠0 from cuspWhittakerHeightFactor_center_ne_zero (3*index i)]
end OAI.CubicEisenstein
