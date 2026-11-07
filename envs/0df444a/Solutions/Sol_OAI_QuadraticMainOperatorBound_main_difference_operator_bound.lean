-- Prove2me | solution 1 for OAI.QuadraticMainOperatorBound.main_difference_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:59:08.689469+00:00
-- url     : https://prove2.me/submissions/0c6e0b2c-79f4-4e6b-8f4c-50517f2b386d

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_ideal_coprime_gram_operator_bound
import Theorems.Thm_OAI_QuadraticMainOperatorBound_mainWeight_norm_le
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealDivisorBound_divisor_ne_zero
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
open scoped BigOperators Classical
open OAI.QuadraticMainOperatorBound
open IdealMobiusDivisorSum QuadraticMainBoundary IdealCoprimeSieveOperator FiniteSieveOperator
namespace OAI.QuadraticMainOperatorBound
theorem _root_.solution {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O)
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ)
    (r : Ideal O → Ideal O → n → ℂ) (hr : ∀ D E j, ‖r D E j‖ ≤ 1) :
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ j, ‖a j‖ ^ 2) := by
  let B := (1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
    ∑ j, ‖a j‖ ^ 2
  have hB : 0 ≤ B := by
    have hC := (supportConstant_pos ε hε).le
    dsimp [B]
    positivity
  have hterm (D : Ideal O) (hD : D ∈ idealDivisors G)
      (E : Ideal O) (hE : E ∈ idealDivisors G) :
      ‖(UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤ B := by
    have hD0 := IdealDivisorBound.divisor_ne_zero hG hD
    have hE0 := IdealDivisorBound.divisor_ne_zero hG hE
    have he := ideal_coprime_gram_operator_bound ε hε column hcol N hN hnorm A
      (fun j => a j * r D E j) (fun i => mainWeight K (H i) D E) (1 / Real.sqrt K)
      (by positivity) (fun i => mainWeight_norm_le K hK (H i) D E hD0 hE0)
    have hm : (∑ j, ‖a j * r D E j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hr D E j)
    have heB : ‖∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0)‖ ≤ B := by
      apply he.trans
      exact mul_le_mul_of_nonneg_left hm (by
        have hC := (supportConstant_pos ε hε).le
        positivity)
    have hmu : ‖(UniqueFactorizationMonoid.moebius E : ℂ)‖ ≤ 1 := by
      unfold UniqueFactorizationMonoid.moebius
      split_ifs <;> simp
    rw [norm_mul]
    calc
      _ ≤ 1 * B := mul_le_mul hmu heB (norm_nonneg _) (by norm_num)
      _ = B := one_mul B
  calc
    _ ≤ ∑ D ∈ idealDivisors G, ‖∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, B := by
      apply Finset.sum_le_sum
      intro D hD
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun E hE => hterm D hD E hE))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, B]; ring
end OAI.QuadraticMainOperatorBound
