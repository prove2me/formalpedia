-- Prove2me | solution 1 for OAI.CoprimeBilinearSieve.coprime_bilinear_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:00:54.033192+00:00
-- url     : https://prove2.me/submissions/a21f17c7-a339-4c54-bfd8-606d95a9bd66

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Theorems.Thm_OAI_CoprimeBilinearSieve_disjoint_bilinear_expansion
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CoprimeSieveOperator_masked_coefficient_energy
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FiniteSieveOperator_energy_bound
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
open OAI.CoprimeBilinearSieve
open FiniteSieveOperator CoprimeSieveOperator CoprimeMobiusExtension
namespace OAI.CoprimeBilinearSieve
theorem _root_.solution {ι m n p : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2) := by
  let X (D : Finset ι) (i : m) : ℂ := ∑ j, A i j * (if D ⊆ left j then a j else 0)
  let Y (D : Finset ι) (i : m) : ℂ := ∑ k, C i k * (if D ⊆ right k then b k else 0)
  have heq (i : m) :
      (∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card * (star (X D i) * Y D i) := by
    simpa only [X, Y, mul_ite, mul_zero] using
      disjoint_bilinear_expansion B left right hl hr (fun j => A i j * a j)
        (fun k => C i k * b k)
  have hnorm :
      (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0‖) ≤
        ∑ D ∈ B.powerset, ∑ i, ‖X D i‖ * ‖Y D i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D _
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_star]
    exact le_rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (B.powerset ×ˢ (Finset.univ : Finset m))
    (fun di => ‖X di.1 di.2‖) (fun di => ‖Y di.1 di.2‖)
  simp only [Finset.sum_product] at hCS
  have hX : (∑ D ∈ B.powerset, ∑ i, ‖X D i‖ ^ 2) ≤
      ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator A‖ ^ 2 *
          ∑ j, ‖if D ⊆ left j then a j else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound A _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B left hl a]
  have hY : (∑ D ∈ B.powerset, ∑ i, ‖Y D i‖ ^ 2) ≤
      ‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator C‖ ^ 2 *
          ∑ k, ‖if D ⊆ right k then b k else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound C _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B right hr b]
  exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2).trans
    (hCS.trans (mul_le_mul hX hY (by positivity) (by positivity)))
end OAI.CoprimeBilinearSieve
