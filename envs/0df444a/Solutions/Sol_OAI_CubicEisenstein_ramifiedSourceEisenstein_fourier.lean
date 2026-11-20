-- Prove2me | solution 1 for OAI.CubicEisenstein.ramifiedSourceEisenstein_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:52.230979+00:00
-- url     : https://prove2.me/submissions/a882e0af-df67-4de4-a316-29d275364b41

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Theorems.Thm_OAI_CubicEisenstein_sourceEisenstein_primitive_lower_four
import Theorems.Thm_OAI_CubicEisenstein_integrable_fixed_left_Eisenstein_fourier
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_diagonal_once_fourier_shift
import Theorems.Thm_OAI_CubicEisenstein_diagonal_unit_fourier_shift
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_onceCusp_eisenstein_fourier
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCuspRoot_primitive
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCuspRoot_val
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCuspScaleUnit_spec
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCusp_direct_base
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCusp_neg_inv_square
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCusp_opposite_base
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCusp_opposite_character
import Theorems.Thm_OAI_CubicEisenstein_ramifiedCusp_unit_base
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_unitCuspDiagonal_one
import Theorems.Thm_OAI_CubicEisenstein_unitCusp_eisenstein_fourier_base
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
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot b:Eis)) • upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*ramifiedCuspGaussSeries b h hf s := by
  let t:=ramifiedCuspRoot b
  let shift:=eisEmbedding (↑t⁻¹:Eis)
  let arch:=(v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v)
  let f0:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
    ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f1:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (-(t:Eis)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f2:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f3:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (onceCuspScale (ramifiedCuspScaleUnit b)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  have hi0:IntegrableOn f0 periodDomain:=by
    simpa only [f0,add_zero] using integrable_fixed_left_Eisenstein_fourier
      (integralComplexMatrix (lowerCuspMatrix (t:Eis))) v hv s hs 0 (ninthCuspFrequency h)
  have hi1:IntegrableOn f1 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi2:IntegrableOn f2 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi3:IntegrableOn f3 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have heq:(∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)) • upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (4:ℂ)⁻¹*((∫z in periodDomain,f0 z)+(∫z in periodDomain,f1 z)+
        (∫z in periodDomain,f2 z)+(∫z in periodDomain,f3 z)):=by
    calc
      _ = ∫z in periodDomain,(4:ℂ)⁻¹*(f0 z+f1 z+f2 z+f3 z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z=>by
          dsimp only
          rw [sourceEisenstein_primitive_lower_four t (ramifiedCuspScaleUnit b)
            (ramifiedCuspRoot_primitive b) (ramifiedCuspScaleUnit_spec b)]
          dsimp only [f0,f1,f2,f3,shift]
          ring)
      _ = _ := by
        rw [integral_const_mul]
        rw [integral_add (f:=fun z=>f0 z+f1 z+f2 z) (g:=f3) ((hi0.add hi1).add hi2) hi3,
          integral_add (f:=fun z=>f0 z+f1 z) (g:=f2) (hi0.add hi1) hi2,
          integral_add (f:=f0) (g:=f1) hi0 hi1]
  have hr0:(↑(1:Eisˣ)⁻¹:Eis)^2*(t:Eis)=omega^(ramifiedCuspDirectIndex b):=by
    simpa [t] using ramifiedCuspRoot_val b
  have hr1:(↑(-t)⁻¹:Eis)^2*((-t:Eisˣ):Eis)=-(omega^(ramifiedCuspOppositeIndex b)):=
    ramifiedCusp_opposite_character b
  have hr2:(↑(-t)⁻¹:Eis)^2*((1:Eisˣ):Eis)=omega^(ramifiedCuspDirectIndex b):=by
    rw [Units.val_one,mul_one,ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  have hb2:(3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*((1:Eisˣ):Eis):=by
    simpa using ramifiedCusp_unit_base b h hf
  have h0:(∫z in periodDomain,f0 z)=arch*unitCuspGaussSeries 1 t h s:=by
    simpa only [unitCuspDiagonal_one,map_one,one_mul,f0,arch] using
      unitCusp_eisenstein_fourier_base 1 t (ramifiedCuspDirectIndex b) h (Or.inl hr0)
        (ramifiedCusp_direct_base b h hf) v hv s hs
  have h1:(∫z in periodDomain,f1 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) (-t) h s):=by
    have he:=diagonal_unit_fourier_shift (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
      (ramifiedCusp_opposite_base b h hf) v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
        (ramifiedCusp_opposite_base b h hf) v hv s hs] at he
    simpa only [f1,Units.val_neg,arch] using he
  have h2:(∫z in periodDomain,f2 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) 1 h s):=by
    have he:=diagonal_unit_fourier_shift (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
      hb2 v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
        hb2 v hv s hs] at he
    simpa only [f2,Units.val_one,arch] using he
  have h3:(∫z in periodDomain,f3 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*onceCuspGaussSeries (-t) (ramifiedCuspScaleUnit b) h hf s):=by
    dsimp only [f3]
    rw [diagonal_once_fourier_shift (-t) (ramifiedCuspScaleUnit b) h hf v hv s shift hs,
      onceCusp_eisenstein_fourier (-t) (ramifiedCuspScaleUnit b) h hf v hv s hs]
  rw [heq,h0,h1,h2,h3]
  dsimp only [ramifiedCuspGaussSeries,arch,shift,t]
  ring
end OAI.CubicEisenstein
