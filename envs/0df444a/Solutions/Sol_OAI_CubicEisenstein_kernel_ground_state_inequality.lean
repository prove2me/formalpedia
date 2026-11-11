-- Prove2me | solution 1 for OAI.CubicEisenstein.kernel_ground_state_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:10:27.146673+00:00
-- url     : https://prove2.me/submissions/f866a436-0835-4049-856f-6a6fc346a4a9

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Theorems.Thm_OAI_CubicEisenstein_kernelGroundStateTest_tsupport
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_field_eq
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedPotential_memLp
import Theorems.Thm_OAI_CubicEisenstein_kernelGroundState_pair_le
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelCompact_smooth_cutoff
import Theorems.Thm_OAI_CubicEisenstein_kernelDirichletForm_supported_equation
import Theorems.Thm_OAI_CubicEisenstein_kernelDirichletPairDensity_integrable
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientEnergyDensity_integrable
import Theorems.Thm_OAI_CubicEisenstein_positiveEuclideanLaplacian_congr
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
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
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
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply


attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ComplexConjugate
namespace OAI.CubicEisenstein
theorem _root_.solution (φ V : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (hV : Continuous V)
    (hPDE : ∀ p : EuclideanSpatial, 0 < p 2 →
      positiveEuclideanLaplacian (fun q => (φ (kernelEuclideanProjection q) : ℂ)) p =
        ((V (kernelEuclideanProjection p)*φ (kernelEuclideanProjection p) : ℝ) : ℂ))
    (f : kernelSmoothTests) :
    (∫ q, V q*‖f.1 q‖^2 ∂integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
  obtain ⟨χ,hχ,hχK,hχone,hχrange⟩ := kernelCompact_smooth_cutoff (tsupport f.1) f.2.2
  let h := kernelTruncatedWeight χ φ hχ hχK hφ
  let g := kernelGroundStateTest φ hφ hpos f
  let A : KernelQuotient → ℂ := fun q => ((χ q*V q*φ q : ℝ) : ℂ)
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    kernelTruncatedPotential_memLp χ φ V hχ.continuous hχK hφ.continuous hV
  have hcoord : ∀ p : EuclideanSpatial, 0 < p 2 →
      kernelEuclideanProjection p ∈ tsupport g.1 →
      kernelCoordinateLaplacian h p = A (kernelEuclideanProjection p) := by
    intro p hp hpg
    have hfmem : kernelEuclideanProjection p ∈ tsupport f.1 :=
      kernelGroundStateTest_tsupport φ hφ hpos f hpg
    have hlocal := hχone (kernelEuclideanProjection p) hfmem
    change positiveEuclideanLaplacian (kernelTestField h) p = _
    rw [positiveEuclideanLaplacian_congr _ _ p
      (kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hlocal),hPDE p hp]
    dsimp only [A]
    rw [hlocal.eq_of_nhds,one_mul]
  have hprod (q : KernelQuotient) : star (A q)*g.1 q = ((V q*‖f.1 q‖^2 : ℝ) : ℂ) := by
    change star ((χ q*V q*φ q : ℝ) : ℂ) * ((‖f.1 q‖^2/φ q : ℝ) : ℂ) = _
    by_cases hfzero : f.1 q = 0
    · simp [hfzero]
    · have hq : q ∈ tsupport f.1 := subset_tsupport f.1 hfzero
      have hχq : χ q = 1 := (hχone q hq).eq_of_nhds
      have hφq : φ q ≠ 0 := (hpos q).ne'
      simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,hχq,one_mul]
      congr 1
      field_simp
  have hgreen : kernelDirichletForm h g =
      ((∫ q, V q*‖f.1 q‖^2 ∂integralQuotientVolume globalKubotaKernel : ℝ) : ℂ) := by
    rw [kernelDirichletForm_supported_equation h g A hA hcoord]
    simp_rw [hprod]
    exact integral_complex_ofReal
  have hbound : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
    exact integral_mono (kernelDirichletPairDensity_integrable h g).re
      (kernelQuotientEnergyDensity_integrable f)
      (fun q => kernelGroundState_pair_le χ φ hχ hχK hφ hpos f hχone q)
  have hreal : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂integralQuotientVolume globalKubotaKernel) = (kernelDirichletForm h g).re := by
    simpa only [kernelDirichletForm,RCLike.re_to_complex] using integral_re (kernelDirichletPairDensity_integrable h g)
  rw [hreal,hgreen,Complex.ofReal_re] at hbound
  exact hbound
end OAI.CubicEisenstein
