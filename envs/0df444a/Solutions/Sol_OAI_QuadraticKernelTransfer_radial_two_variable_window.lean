-- Prove2me | solution 1 for OAI.QuadraticKernelTransfer.radial_two_variable_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:13:42.53599+00:00
-- url     : https://prove2.me/submissions/517a673c-a068-4111-963b-b070bf15b93a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_log_separation_envelope
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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticKernelTransfer
open FourierBridge EisensteinSchwartzPoisson
namespace OAI.QuadraticKernelTransfer
theorem _root_.solution (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, |x| ≤ L₁ → |y| ≤ L₂ →
        paperRadialFourier W (R * Real.exp (x+y)) =
          ∫ t, logPhase t x * logPhase t y * b t) ∧
      (1 + R) ^ A * (∫ t, ‖b t‖) ≤ C := by
  let V₁ : ℝ → ℂ := fun x => if |x| ≤ L₁ then 1 else 0
  let V₂ : ℝ → ℂ := fun x => if |x| ≤ L₂ then 1 else 0
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let lengthScale : Bool → ℝ := fun j => if j then L₂ else L₁
  have hL : ∀ j, 0 ≤ lengthScale j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ lengthScale j := by
    intro j x h
    cases j
    · change |x| ≤ L₁
      change (if |x| ≤ L₁ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
    · change |x| ≤ L₂
      change (if |x| ≤ L₂ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W V (fun _ => 1) lengthScale hL hV A 0
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, hmass, _⟩ := hs R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y hx hy
    have h := hb (fun j => if j then y else x)
    simpa only [V, V₁, V₂, lengthScale, Fintype.prod_bool, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte, if_pos hx, if_pos hy, one_mul, mul_one,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  · simpa only [pow_zero, one_mul] using hmass
end OAI.QuadraticKernelTransfer
