-- Prove2me | solution 1 for OAI.QuadraticInitialBound.quadratic_initial_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:40:18.669492+00:00
-- url     : https://prove2.me/submissions/31e9099f-4d6b-4cc0-b2c4-93f2678ee8ba

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Theorems.Thm_OAI_QuadraticInitialBound_quadratic_gram_offdiagonal_of_norm_le
import Theorems.Thm_OAI_QuadraticInitialBound_quadratic_gram_diagonal
import Theorems.Thm_OAI_QuadraticInitialBound_quadratic_mean_expand
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_QuadraticInitialBound_pvControl_nonneg
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.QuadraticInitialBound
theorem _root_.solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (quadratic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact quadratic_gram_offdiagonal_of_norm_le P hinj hg hc _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq,  hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [quadratic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring
end OAI.QuadraticInitialBound
