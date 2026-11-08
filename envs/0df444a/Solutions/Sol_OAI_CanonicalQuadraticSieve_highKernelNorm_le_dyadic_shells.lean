-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.highKernelNorm_le_dyadic_shells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:31:50.446978+00:00
-- url     : https://prove2.me/submissions/cb395496-920a-4b84-a4d8-7eb03ad72c3c

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
import Theorems.Thm_OAI_CanonicalQuadraticSieve_highKernelShellNorm_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_highKernel_dyadic_cover
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FiniteSieveOperator_energy_bound
import Theorems.Thm_OAI_FiniteSieveOperator_squared_norm_le_of_energy
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
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
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K : ℝ) (lengthScale : ℕ) (hML : M ≤ (2 : ℝ) ^ lengthScale) :
    highKernelNorm M N K ≤ ∑ j ∈ Finset.range (lengthScale + 1), highKernelShellNorm ((2 : ℝ) ^ j) N K := by
  apply squared_norm_le_of_energy _ _ (Finset.sum_nonneg (fun j _ => highKernelShellNorm_nonneg _ _ _))
  intro a
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hE (I : Ideal O) : 0 ≤ E I := sq_nonneg _
  change (∑ I : highKernelRange M K, E I.val) ≤ _
  rw [Finset.sum_coe_sort (highKernelRange M K) E]
  calc
    _ ≤ ∑ I ∈ highKernelRange M K, ∑ j ∈ Finset.range (lengthScale + 1),
        if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨j, hj, hIj⟩ := highKernel_dyadic_cover M K lengthScale hML I hI
      have h := Finset.single_le_sum (s := Finset.range (lengthScale + 1))
        (f := fun j => if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0)
        (fun _ _ => by split_ifs <;> positivity) hj
      simpa only [if_pos hIj] using h
    _ = ∑ j ∈ Finset.range (lengthScale + 1), ∑ I ∈ highKernelRange M K,
        if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0 := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (lengthScale + 1), ∑ I ∈ highKernelShellRange ((2 : ℝ) ^ j) K, E I := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro I hI
        exact (Finset.mem_filter.mp hI).2
      · intro I hI hnot
        exact hE I
    _ ≤ ∑ j ∈ Finset.range (lengthScale + 1), highKernelShellNorm ((2 : ℝ) ^ j) N K * ∑ J, ‖a J‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_coe_sort (highKernelShellRange ((2 : ℝ) ^ j) K) E]
      exact FiniteSieveOperator.energy_bound (highKernelShellMatrix ((2 : ℝ) ^ j) N K) a
    _ = _ := (Finset.sum_mul ..).symm
end OAI.CanonicalQuadraticSieve
