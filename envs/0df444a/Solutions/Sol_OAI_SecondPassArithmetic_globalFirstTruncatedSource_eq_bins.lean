-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstTruncatedSource_eq_bins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:33:21.912909+00:00
-- url     : https://prove2.me/submissions/65183aea-155c-4916-b267-8d02ed6f6181

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_first
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinFirstCoefficient_first
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstSupportedPool_index_mem_box
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTruncatedSource_eq_supported
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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    globalFirstTruncatedSource p hp hg hinj pool s
      (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m g W ell side
      (globalFirstPooledRow p K ell B F side) =
      ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinFirstCoefficient K ell B F j : ℂ)*
          globalSecondLiteralBinSource p hp hcop hg (fun x => w x.first) source side j pool Ψ m
            g g W ell (globalPooledRowScale K ell B F j) := by
  dsimp only
  rw [globalFirstTruncatedSource_eq_supported p hp hcop hg hinj hc hpr]
  · let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    have hmap : ∀ x∈source,globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) :=
      fun x hx => globalFirstSupportedPool_index_mem_box p hp pool s hs K ell B F M H hK hell hB hF hH side hb₁ hb₂ x hx
    change (∑ ray : SecondRayIndex,∑ x∈source,
      (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x) = _
    simp only [globalSecondLiteralBinSource,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ray hray
    have hsplit := Finset.sum_fiberwise_of_maps_to hmap
      (fun x => (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x)
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro x hx
    have hxj := (Finset.mem_filter.mp hx).2
    have hy := globalPooledRowScale_first p K ell B F side x
    have hc' := globalBinFirstCoefficient_first p K ell B F side x
    rw [hxj] at hy hc'
    rw [← hy,← hc']
    ring
  · exact hell
  · exact hgM
end OAI.SecondPassArithmetic
