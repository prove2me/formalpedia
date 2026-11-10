-- Prove2me | solution 1 for OAI.CompletedGauss.reflectionConductorCost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:20:48.117546+00:00
-- url     : https://prove2.me/submissions/ec4b3be2-b2d1-4b2a-84d0-ab72217ab287

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
import Theorems.Thm_OAI_CompletedGauss_nonresidual_gain_product_dvd
import Theorems.Thm_OAI_CompletedGauss_reflectionConductorCost_eq_prod
import Theorems.Thm_OAI_CompletedGauss_reflectionLocalCost_nonneg
import Theorems.Thm_OAI_CompletedGauss_reflectionLocalCost_le_gain
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CompletedGauss_rowPowerfulPart_ne_zero
import Theorems.Thm_OAI_CompletedGauss_squarefreeMaskPart_ne_zero
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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid
open ActualEisensteinCubic UniqueFactorizationMonoid
namespace OAI.CompletedGauss
theorem _root_.solution {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr
end OAI.CompletedGauss
