-- Prove2me | solution 1 for OAI.LocalLogFourier.coupled_double_positive_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:08:27.905493+00:00
-- url     : https://prove2.me/submissions/099c694c-293f-45e9-9a83-9bfa1b4cb268

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_LocalLogFourier_coupled_positive_log_separation_uniform
import Theorems.Thm_OAI_FourierBridge_logPhase_sum

attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply

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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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
open OAI.LocalLogFourier
namespace OAI.LocalLogFourier
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : ℝ → ℂ)
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos₁ : ContDiffOn ℝ ∞ F₁ (Set.Ioi 0))
    (hFpos₂ : ContDiffOn ℝ ∞ F₂ (Set.Ioi 0))
    (A₁ A₂ J₁ J₂ : ℕ) (CF₁ CF₂ : ℝ)
    (hCF₁ : 0 ≤ CF₁) (hCF₂ : 0 ≤ CF₂)
    (hEuler₁ : ∀ i ≤ J₁ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₁ * ‖eulerDeriv F₁ i x‖ ≤ CF₁)
    (hEuler₂ : ∀ i ≤ J₂ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₂ * ‖eulerDeriv F₂ i x‖ ≤ CF₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ →
        ∃ (b₁ b₂ : ℝ → ℂ),
          (∀ y : ι → ℝ,
            (∏ j : ι, W j (y j)) *
              F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
              F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
            ∫ t₁ : ℝ, (∫ t₂ : ℝ,
              (∏ j : ι, W j (y j)) *
                FourierBridge.logPhase t₁ (∑ j : ι, a₁ j * y j) *
                FourierBridge.logPhase t₂ (∑ j : ι, a₂ j * y j) *
                b₂ t₂) * b₁ t₁) ∧
          ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
            ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
             (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖)) ≤ C := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ :=
    coupled_positive_log_separation_uniform W F₁ a₁ M
      hM hWwindow hFpos₁ A₁ J₁ CF₁ hCF₁ hEuler₁
  obtain ⟨C₂, hC₂, h₂⟩ :=
    coupled_positive_log_separation_uniform W F₂ a₂ M
      hM hWwindow hFpos₂ A₂ J₂ CF₂ hCF₂ hEuler₂
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₁, hsep₁, hbound₁⟩ := h₁ R₁ hR₁
  obtain ⟨b₂, hsep₂, hbound₂⟩ := h₂ R₂ hR₂
  refine ⟨b₁, b₂, ?_, ?_⟩
  · intro y
    let P : ℂ := ∏ j : ι, W j (y j)
    let s₁ : ℝ := ∑ j : ι, a₁ j * y j
    let s₂ : ℝ := ∑ j : ι, a₂ j * y j
    let Z₁ : ℂ := F₁ (R₁ * Real.exp s₁)
    let Z₂ : ℂ := F₂ (R₂ * Real.exp s₂)
    have hphase₁ (t : ℝ) :
        (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a₁ j * y j)) =
          P * FourierBridge.logPhase t s₁ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₁]
      congr 1
      simpa using (FourierBridge.logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₁ j * y j)).symm
    have hphase₂ (t : ℝ) :
        (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a₂ j * y j)) =
          P * FourierBridge.logPhase t s₂ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₂]
      congr 1
      simpa using (FourierBridge.logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₂ j * y j)).symm
    have hsep₁' : P * Z₁ =
        ∫ t₁ : ℝ, (P * FourierBridge.logPhase t₁ s₁) * b₁ t₁ := by
      simpa only [P, Z₁, s₁, hphase₁] using hsep₁ y
    have hsep₂' : P * Z₂ =
        ∫ t₂ : ℝ, (P * FourierBridge.logPhase t₂ s₂) * b₂ t₂ := by
      simpa only [P, Z₂, s₂, hphase₂] using hsep₂ y
    have hinner (t₁ : ℝ) :
        P * FourierBridge.logPhase t₁ s₁ * Z₂ =
          ∫ t₂ : ℝ,
            (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
              b₂ t₂ := by
      calc
        P * FourierBridge.logPhase t₁ s₁ * Z₂ =
            FourierBridge.logPhase t₁ s₁ * (P * Z₂) := by ring
        _ = FourierBridge.logPhase t₁ s₁ *
            (∫ t₂ : ℝ, (P * FourierBridge.logPhase t₂ s₂) * b₂ t₂) := by
              rw [hsep₂']
        _ = ∫ t₂ : ℝ,
            FourierBridge.logPhase t₁ s₁ *
              ((P * FourierBridge.logPhase t₂ s₂) * b₂ t₂) := by
                rw [integral_const_mul]
        _ = ∫ t₂ : ℝ,
            (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
              b₂ t₂ := by
                apply integral_congr_ae
                filter_upwards [] with t₂
                ring
    change P * Z₁ * Z₂ = _
    calc
      P * Z₁ * Z₂ =
          (∫ t₁ : ℝ, (P * FourierBridge.logPhase t₁ s₁) * b₁ t₁) * Z₂ := by
            rw [hsep₁']
      _ = ∫ t₁ : ℝ,
          ((P * FourierBridge.logPhase t₁ s₁) * b₁ t₁) * Z₂ := by
            rw [integral_mul_const]
      _ = ∫ t₁ : ℝ,
          (P * FourierBridge.logPhase t₁ s₁ * Z₂) * b₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            ring
      _ = ∫ t₁ : ℝ, (∫ t₂ : ℝ,
          (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
            b₂ t₂) * b₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            rw [hinner t₁]
  · let I₁ : ℝ := ∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖
    let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖
    have hI₁ : 0 ≤ I₁ := by
      dsimp [I₁]
      apply integral_nonneg
      intro t
      positivity
    have hI₂ : 0 ≤ I₂ := by
      dsimp [I₂]
      apply integral_nonneg
      intro t
      positivity
    have hP₁ : 0 ≤ (1 + R₁) ^ A₁ := pow_nonneg (by linarith) _
    have hP₂ : 0 ≤ (1 + R₂) ^ A₂ := pow_nonneg (by linarith) _
    have hmul : ((1 + R₁) ^ A₁ * I₁) *
        ((1 + R₂) ^ A₂ * I₂) ≤ C₁ * C₂ := by
      exact mul_le_mul hbound₁ hbound₂
        (mul_nonneg hP₂ hI₂) hC₁
    simpa only [I₁, I₂, mul_comm, mul_left_comm, mul_assoc] using hmul
end OAI.LocalLogFourier
