-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.product_quadratic_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:43:54.119841+00:00
-- url     : https://prove2.me/submissions/b1dfefa5-a896-4f79-b0ed-f71ba8f0595c

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_productColumnCoefficient_norm
import Theorems.Thm_OAI_CanonicalQuadraticSieve_productColumnCoefficient_row_sum
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_bounded_supported_quadratic_norm
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
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealDivisorBound_ideal_divisor_small_power
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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,Supported I ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_supported_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : Supported I ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨(supported_mul_iff n b).mpr ⟨(hS n hm.1).1,(hT b hm.2).1⟩,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1.1).trans
    apply (hdiv I (hp I hI).1.1).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X^(ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X)^(ε/2)*(X^(ε/4))^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^(ε/2)*((K*X)^(ε/4))^2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0<K*X),←Real.rpow_add (by positivity : 0<K*X)]
        congr 1
        ring
  calc
    _ = (C*D^2)*((K*X)^(ε/2)*(X^(ε/4))^2)*(K+X)*X := by ring
    _ ≤ _ := by change _≤(C*D^2)*(K*X)^ε*(K+X)*X; gcongr
end OAI.CanonicalQuadraticSieve
