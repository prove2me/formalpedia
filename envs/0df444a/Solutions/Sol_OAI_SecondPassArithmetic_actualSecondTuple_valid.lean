-- Prove2me | solution 1 for OAI.SecondPassArithmetic.actualSecondTuple_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:59:19.380634+00:00
-- url     : https://prove2.me/submissions/22dd3e9a-931b-4ea4-b1b6-acf2684878db

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrimePools
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyBlocks
import Theorems.Thm_OAI_SecondPassArithmetic_span_dvd_of_element_dvd
import Theorems.Thm_OAI_SecondPassArithmetic_primeProduct_add
import Theorems.Thm_OAI_SecondPassArithmetic_aLabel_dvd_primeProduct
import Theorems.Thm_OAI_SecondPassArithmetic_cubeRadical_dvd_jLabel_b0
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_cube_product_decomposition
import Theorems.Thm_OAI_FirstPassCubeLabels_jLabel_eq_squarefree_mul_j2
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
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
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SecondPassArithmetic
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
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (B C D E V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C ∪ B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (k : O) :
    SecondPassFiber.Valid (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k)
      (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (actualSecondRow p D E k) := by
  have hJ := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2 p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
  have hb := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.cube_product_decomposition p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [primeProduct_add] at hb
  have hA₁ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₁ hv)
  have hA₂ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₂ hv)
  rw [primeProduct_add, ← Ideal.span_singleton_mul_span_singleton] at hA₁ hA₂
  have hrad := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [← Ideal.span_singleton_mul_span_singleton] at hrad
  have hD' : (∏ i ∈ D, Ideal.span {p i}) ∣
      (∏ i ∈ C, Ideal.span {p i}) * Ideal.span {cubeRadical p B} := by
    have hh := Finset.prod_dvd_prod_of_subset D (C ∪ B) (fun i => (Ideal.span {p i} : Ideal O)) hD
    rw [Finset.prod_union hCB] at hh
    simpa only [cubeRadical, FiniteGaussPhase.span_finset_prod] using hh
  have hD'' := hD'.trans (mul_dvd_mul_left (∏ i ∈ C, (Ideal.span {p i} : Ideal O)) hrad)
  constructor
  · rfl
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} =
          Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
    simpa only [← Ideal.span_singleton_mul_span_singleton] using hJ.symm
  · change Ideal.span {primeProduct p B v₁} * Ideal.span {primeProduct p B v₂} =
        Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)}
    simpa only [pow_two, ← Ideal.span_singleton_mul_span_singleton] using hb
  · exact hA₁
  · exact hA₂
  · apply hD''.trans
    refine ⟨(∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i}), ?_⟩
    simp only [actualSecondLabel]
    ring
  · rfl
end OAI.SecondPassArithmetic
