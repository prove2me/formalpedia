-- Prove2me | solution 1 for OAI.FourierBridge.coupled_double_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:14:35.281204+00:00
-- url     : https://prove2.me/submissions/5af2f660-3a7b-4e24-862c-200ea6b9462a

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_FourierBridge_coupled_log_separation
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.FourierBridge
open scoped ContDiff FourierTransform SchwartzMap
namespace OAI.FourierBridge
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ V₁ V₂ : ℝ → ℂ)
    (R₁ R₂ : ℝ) (a₁ a₂ y : ι → ℝ)
    (hV₁c : HasCompactSupport V₁) (hV₁s : ContDiff ℝ ∞ V₁)
    (hF₁s : ContDiff ℝ ∞ F₁)
    (hV₂c : HasCompactSupport V₂) (hV₂s : ContDiff ℝ ∞ V₂)
    (hF₂s : ContDiff ℝ ∞ F₂)
    (hactive₁ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₁ (∑ j : ι, a₁ j * y j) = 1)
    (hactive₂ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₂ (∑ j : ι, a₂ j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
      F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
      ∫ t₁ : ℝ,
        (∫ t₂ : ℝ,
          (∏ j : ι,
            W j (y j) * logPhase t₁ (a₁ j * y j) *
              logPhase t₂ (a₂ j * y j)) *
            (𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)) t₂) *
          (𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)) t₁ := by
  classical
  let P : ℂ := ∏ j : ι, W j (y j)
  let Z₁ : ℂ := F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j))
  let Z₂ : ℂ := F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j))
  let b₁ := 𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)
  let b₂ := 𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)
  let Q (t₁ : ℝ) : ℂ :=
    ∏ j : ι, W j (y j) * logPhase t₁ (a₁ j * y j)
  let T (t₁ t₂ : ℝ) : ℂ :=
    ∏ j : ι,
      W j (y j) * logPhase t₁ (a₁ j * y j) *
        logPhase t₂ (a₂ j * y j)
  have hsep₁ : P * Z₁ = ∫ t₁ : ℝ, Q t₁ * b₁ t₁ := by
    simpa [P, Z₁, Q, b₁] using
      coupled_log_separation W F₁ V₁ R₁ a₁ y
        hV₁c hV₁s hF₁s hactive₁
  have hsep₂ (t₁ : ℝ) :
      Q t₁ * Z₂ = ∫ t₂ : ℝ, T t₁ t₂ * b₂ t₂ := by
    let W' : ι → ℝ → ℂ :=
      fun j z => W j z * logPhase t₁ (a₁ j * z)
    have hP : (∏ j : ι, W' j (y j)) = Q t₁ := rfl
    have hactive₂' : (∏ j : ι, W' j (y j)) ≠ 0 →
        V₂ (∑ j : ι, a₂ j * y j) = 1 := by
      intro hW'
      have hprod : (∏ j : ι, W j (y j)) ≠ 0 := by
        intro hz
        have hz' : (∏ j : ι, W' j (y j)) = 0 := by
          rw [show (∏ j : ι, W' j (y j)) =
            (∏ j : ι, W j (y j)) *
              (∏ j : ι, logPhase t₁ (a₁ j * y j)) by
                simp [W', Finset.prod_mul_distrib]]
          simp [hz]
        exact hW' hz'
      exact hactive₂ hprod
    simpa [W', Q, T, Z₂, b₂] using
      coupled_log_separation W' F₂ V₂ R₂ a₂ y
        hV₂c hV₂s hF₂s hactive₂'
  calc
    P * Z₁ * Z₂ = (∫ t₁ : ℝ, Q t₁ * b₁ t₁) * Z₂ := by rw [hsep₁]
    _ = ∫ t₁ : ℝ, (Q t₁ * b₁ t₁) * Z₂ := by rw [integral_mul_const]
    _ = ∫ t₁ : ℝ, (Q t₁ * Z₂) * b₁ t₁ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      ring
    _ = ∫ t₁ : ℝ,
          (∫ t₂ : ℝ, T t₁ t₂ * b₂ t₂) * b₁ t₁ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      rw [hsep₂ t₁]
end OAI.FourierBridge
