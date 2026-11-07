-- Prove2me | solution 1 for OAI.QuadraticMainTermDifference.actual_main_terms_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:40:14.225485+00:00
-- url     : https://prove2.me/submissions/a538417d-6d9f-4d44-aeb2-35037444d3e6

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Theorems.Thm_OAI_QuadraticMainTermDifference_sum_powerset_disjoint_union
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticDivisorCancellation_actual_double_divisor_cancellation_coprime
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open scoped BigOperators Classical
open OAI.QuadraticMainTermDifference
open ActualEisensteinCubic QuadraticDivisorCancellation QuadraticMainBoundary
namespace OAI.QuadraticMainTermDifference
theorem _root_.solution {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T G : Finset κ) (hTG : Disjoint T G) (K : ℝ)
    (havoid : ∀ i ∈ G, ∀ j ∈ S, q i ∉ P j) :
    partialSquarefreeSum P hg S q K (T ∪ G) * divisorSum P hg S q G -
      partialSquarefreeSum P hg S q K T *
        (∏ i ∈ G, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) =
      ∑ H ∈ T.powerset, ∑ D ∈ G.powerset, ∑ E ∈ G.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ H, q i) * (∏ i ∈ D, q i) * ∏ i ∈ E, q i) *
        (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
          (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by
  have hdensity := actual_double_divisor_cancellation_coprime P hg S q hprime hinj
    G ∅ (by simp) havoid
  simp only [Finset.union_empty, Finset.powerset_empty, Finset.sum_singleton,
    Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    normalizedRow_one, mul_one] at hdensity
  rw [← hdensity]
  unfold partialSquarefreeSum divisorSum
  rw [sum_powerset_disjoint_union T G hTG]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H hH
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHD : Disjoint H D := hTG.mono (Finset.mem_powerset.mp hH) (Finset.mem_powerset.mp hD)
  have hc : normCutoff q K (H ∪ D) - normCutoff q K H =
      (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
        (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by
    simp only [normCutoff, Finset.prod_union hHD, cutoffDifference, Complex.ofReal_sub]
    split_ifs <;> norm_num
  simp only [Finset.prod_union hHD, normalizedRow_mul]
  rw [← hc]
  ring
end OAI.QuadraticMainTermDifference
