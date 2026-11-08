-- Prove2me | solution 1 for OAI.SecondPassArithmetic.secondExpansionSource_singleton_zero_of_not_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:05:01.77023+00:00
-- url     : https://prove2.me/submissions/d490effb-690a-4f7f-bcb6-fbb5b1b3ccb5

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GreenIntegrals
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GreenIdentity
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_union
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
import Theorems.Thm_OAI_SecondPassArithmetic_normalizedColumn_subset_norm_bound
import Theorems.Thm_OAI_SecondPassArithmetic_secondMaskQuotient_spec
import Theorems.Thm_OAI_SecondPassArithmetic_secondPreColumn_zero_of_common_overlap
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
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
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hs : ¬ SecondSourceSupport p X M x) :
    secondExpansionSource p hp hcop hg F Ψ m c d z {x}
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y = 0 := by
  by_cases hd : Disjoint x.sourceCommon x.overlap
  · have hb : ¬ primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M :=
      fun hb => hs ⟨hd,hb⟩
    have hz (N : Finset ι) :
        normalizedColumn p (fun A => g (columnLog p X A))
          (x.sourceCommon ∪ (x.overlap ∪ N)) = 0 := by
      by_contra hn
      have h := normalizedColumn_subset_norm_bound p hp g M X hX hgM
        x.sourceCommon (x.overlap ∪ N) (x.sourceCommon ∪ x.overlap)
        (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left) hn
      rw [FirstPassCubeLabels.primeProductNorm_union p _ _ hd] at h
      exact hb h
    simp only [secondExpansionSource, Finset.sum_singleton]
    have hk : secondChildKernelPair p hp hcop hg F x.overlap
        (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (-x.frequency)
        (secondSourcePairKernel p
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S))
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S)) W Y) = 0 := by
      unfold secondChildKernelPair
      apply Finset.sum_eq_zero
      intro N hN
      apply Finset.sum_eq_zero
      intro Q hQ
      simp only [secondSourcePairKernel, hz N, star_zero, zero_mul, zero_div, mul_zero]
    rw [hk]
    ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj
      (secondRayPlus Ψ z) m c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      (-x.frequency) (fun _ => 1) x.sourceCommon x.overlap (fun h => hd h.symm)
    rw [secondMaskQuotient_spec p x.divisor x.sourceCommon hE] at hz
    simp only [secondExpansionSource, Finset.sum_singleton,
      secondExpansionQuotient_of_subset p x hE, secondTotalWeight, secondCommonWeight, hz,
      mul_zero, zero_mul]
end OAI.SecondPassArithmetic
