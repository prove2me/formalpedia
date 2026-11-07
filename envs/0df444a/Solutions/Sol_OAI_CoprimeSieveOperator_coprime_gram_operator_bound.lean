-- Prove2me | solution 1 for OAI.CoprimeSieveOperator.coprime_gram_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:52:14.052307+00:00
-- url     : https://prove2.me/submissions/d4c583af-9484-4f21-ae44-1551275a761b

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_CoprimeSieveOperator_disjoint_gram_expansion
import Theorems.Thm_OAI_CoprimeSieveOperator_masked_coefficient_energy
import Theorems.Thm_OAI_CoprimeSieveOperator_weighted_energy_bound
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
open OAI.CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension
namespace OAI.CoprimeSieveOperator
theorem _root_.solution {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  have heq : (∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ) := by
    simp_rw [disjoint_gram_expansion B support hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro i _
    have hz : (∑ j, if D ⊆ support j then A i j * a j else 0) =
        ∑ j, A i j * (if D ⊆ support j then a j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [hz]
    ring
  rw [heq]
  calc
    _ ≤ ∑ D ∈ B.powerset, ‖(-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ B.powerset,
        W * ‖operator A‖ ^ 2 * ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro D _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact weighted_energy_bound A (fun j => if D ⊆ support j then a j else 0) w W hW hw
    _ = _ := by
      rw [← Finset.mul_sum, masked_coefficient_energy B support hs a]
end OAI.CoprimeSieveOperator
