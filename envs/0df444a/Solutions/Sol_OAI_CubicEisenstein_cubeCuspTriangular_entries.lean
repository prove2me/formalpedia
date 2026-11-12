-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeCuspTriangular_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:31:02.307966+00:00
-- url     : https://prove2.me/submissions/d3063aab-07e2-4305-be24-7955fd7ecfc4

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_cubeAverageMatrix_entries
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
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
open scoped Classical MatrixGroups BigOperators
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val ∧
    cubeCuspTriangular d hp 1 0=0 ∧
    cubeCuspTriangular d hp 1 1=(cubeDilationRoot p)⁻¹*eisEmbedding p^(3-d.exponent.val) := by
  let B:=cubeAverageMatrix p hp q*integralComplexMatrix A
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  have hx:eisEmbedding (A 0 0)+3*eisEmbedding q*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    simpa only [map_add,map_mul,map_pow,map_ofNat] using congrArg eisEmbedding d.first
  have hy:eisEmbedding p^3*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    simpa only [map_mul,map_pow] using congrArg eisEmbedding d.second
  have hB0:B 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 0 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    linear_combination (cubeDilationRoot p)⁻¹*hx
  have hB1:B 1 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 1 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.cons_val_one,
      Matrix.cons_val_zero,Matrix.cons_val_fin_one,Matrix.of_apply,zero_mul,zero_add]
    rw [mul_assoc,←hy,←he]
    field_simp
  have hinv:(integralComplexMatrix d.matrix : Matrix (Fin 2) (Fin 2) ℂ)⁻¹=
      !![eisEmbedding (d.matrix 1 1),-eisEmbedding (d.matrix 0 1);
        -eisEmbedding (d.matrix 1 0),eisEmbedding (d.matrix 0 0)] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
    rfl
  have hT:cubeCuspTriangular d hp=(integralComplexMatrix d.matrix)⁻¹*B:=by
    dsimp [cubeCuspTriangular,B]
    group
  have hdet:eisEmbedding (d.matrix 0 0)*eisEmbedding (d.matrix 1 1)-
      eisEmbedding (d.matrix 0 1)*eisEmbedding (d.matrix 1 0)=1:=by
    have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
      simpa only [Matrix.det_fin_two] using d.matrix.property
    simpa only [map_sub,map_mul,map_one] using congrArg eisEmbedding hd
  have h00:cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    linear_combination (cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*hdet
  have h10:cubeCuspTriangular d hp 1 0=0:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    ring
  refine ⟨h00,h10,?_⟩
  have hd:cubeCuspTriangular d hp 0 0*cubeCuspTriangular d hp 1 1=1:=by
    simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using (cubeCuspTriangular d hp).property
  rw [h00] at hd
  have hnon:(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val≠0:=
    mul_ne_zero (inv_ne_zero hz) (pow_ne_zero _ (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ hnon
  rw [hd]
  have hpow:eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val)=eisEmbedding p^3:=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  calc
    1=(cubeDilationRoot p)⁻¹^2*eisEmbedding p^3:=by rw [←he,inv_pow,inv_mul_cancel₀ (pow_ne_zero 2 hz)]
    _=_:=by rw [←hpow];ring
end OAI.CubicEisenstein
