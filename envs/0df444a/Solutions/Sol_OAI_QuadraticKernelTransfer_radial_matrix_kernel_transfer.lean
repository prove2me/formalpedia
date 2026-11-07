-- Prove2me | solution 1 for OAI.QuadraticKernelTransfer.radial_matrix_kernel_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:19:18.214981+00:00
-- url     : https://prove2.me/submissions/20795058-d79f-444f-b0be-98d8191c5872

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_QuadraticKernelTransfer_sum_norm_integral_bound
import Theorems.Thm_OAI_QuadraticKernelTransfer_radial_two_variable_window
import Theorems.Thm_OAI_QuadraticKernelTransfer_radial_phase_integrable
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FourierBridge_logPhase_norm
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n]
        (c : m → n → ℂ) (x : m → ℝ) (y : n → ℝ) (H : ℝ),
        0 ≤ H → (∀ i, |x i| ≤ L₁) → (∀ j, |y j| ≤ L₂) →
        (∀ t, (∑ i, ‖∑ j, c i j * logPhase t (y j)‖) ≤ H) →
        (1 + R) ^ A * (∑ i, ‖∑ j, c i j *
          paperRadialFourier W (R * Real.exp (x i + y j))‖) ≤ C * H := by
  obtain ⟨C, hC, hs⟩ := radial_two_variable_window W L₁ L₂ hL₁ hL₂ A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ c x y H hH hx hy hphase
  obtain ⟨b, hb, hmass⟩ := hs R hR
  let φ : m → ℝ → ℂ := fun i t => logPhase t (x i) * ∑ j, c i j * logPhase t (y j)
  have hint (i : m) : Integrable (fun t => b t * φ i t) := by
    have h := integrable_finsetSum (Finset.univ : Finset n)
      (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))
    simpa only [φ, Finset.mul_sum] using h
  have hid (i : m) : (∑ j, c i j * paperRadialFourier W (R * Real.exp (x i + y j))) =
      ∫ t, b t * φ i t := by
    rw [show (fun t => b t * φ i t) = fun t =>
      ∑ j, b t * (logPhase t (x i) * (c i j * logPhase t (y j))) by
        funext t; simp only [φ, Finset.mul_sum]]
    rw [integral_finsetSum _ (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb _ _ (hx i) (hy j), ← integral_const_mul]
    congr 1
    funext t
    ring
  have hp (t : ℝ) : (∑ i, ‖φ i t‖) ≤ H := by
    simpa only [φ, norm_mul, logPhase_norm, one_mul] using hphase t
  have hi := sum_norm_integral_bound b φ H hint b.integrable.norm hp
  simp only [← hid] at hi
  calc
    _ ≤ (1 + R) ^ A * (H * ∫ t, ‖b t‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = H * ((1 + R) ^ A * ∫ t, ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := mul_comm _ _
end OAI.QuadraticKernelTransfer
