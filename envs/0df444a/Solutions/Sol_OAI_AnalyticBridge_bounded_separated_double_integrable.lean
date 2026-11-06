-- Prove2me | solution 1 for OAI.AnalyticBridge.bounded_separated_double_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:03.65822+00:00
-- url     : https://prove2.me/submissions/cf73e3fd-db4a-4719-9c7c-bdfd4780939e

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly

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
open OAI.AnalyticBridge
open scoped FourierTransform SchwartzMap
namespace OAI.AnalyticBridge
theorem _root_.solution
    {Ω : Type*} (S : Finset Ω)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (u v : Ω → ℝ → ℂ)
    (humeas : ∀ ω ∈ S, AEStronglyMeasurable (u ω) volume)
    (hvmeas : ∀ ω ∈ S, AEStronglyMeasurable (v ω) volume)
    (hubdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖u ω t‖ ≤ M)
    (hvbdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖v ω t‖ ≤ M) :
    (∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ =>
        (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) volume) ∧
    (∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        (𝓕 g₁) t₁ *
          (∫ t₂ : ℝ,
            (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂))) volume) := by
  have hb₁ : Integrable (fun t : ℝ => (𝓕 g₁) t) volume :=
    (𝓕 g₁).integrable
  have hb₂ : Integrable (fun t : ℝ => (𝓕 g₂) t) volume :=
    (𝓕 g₂).integrable
  have hvint (ω : Ω) (hω : ω ∈ S) :
      Integrable (fun t₂ : ℝ => (𝓕 g₂) t₂ * v ω t₂) volume := by
    obtain ⟨Mv, hMv⟩ := hvbdd ω hω
    exact hb₂.mul_bdd (hvmeas ω hω)
      (Filter.Eventually.of_forall hMv)
  constructor
  · intro t₁ ω hω
    have hmeas : AEStronglyMeasurable
        (fun t₂ : ℝ => u ω t₁ * v ω t₂) volume :=
      (hvmeas ω hω).const_mul (u ω t₁)
    obtain ⟨Mv, hMv⟩ := hvbdd ω hω
    have hbound : ∀ t₂ : ℝ,
        ‖u ω t₁ * v ω t₂‖ ≤ ‖u ω t₁‖ * Mv := by
      intro t₂
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMv t₂) (norm_nonneg _)
    exact hb₂.mul_bdd hmeas (Filter.Eventually.of_forall hbound)
  · intro ω hω
    let Cv : ℂ := ∫ t₂ : ℝ, (𝓕 g₂) t₂ * v ω t₂
    have hfactor (t₁ : ℝ) :
        (∫ t₂ : ℝ,
          (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) = u ω t₁ * Cv := by
      calc
        (∫ t₂ : ℝ,
          (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) =
            ∫ t₂ : ℝ, u ω t₁ * ((𝓕 g₂) t₂ * v ω t₂) := by
          apply integral_congr_ae
          filter_upwards [] with t₂
          ring
        _ = u ω t₁ * Cv := by rw [integral_const_mul]
    obtain ⟨Mu, hMu⟩ := hubdd ω hω
    have hmeas : AEStronglyMeasurable
        (fun t₁ : ℝ => u ω t₁ * Cv) volume :=
      (humeas ω hω).mul_const Cv
    have hbound : ∀ t₁ : ℝ,
        ‖u ω t₁ * Cv‖ ≤ Mu * ‖Cv‖ := by
      intro t₁
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hMu t₁) (norm_nonneg _)
    have hInt : Integrable
        (fun t₁ : ℝ => (𝓕 g₁) t₁ * (u ω t₁ * Cv)) volume :=
      hb₁.mul_bdd hmeas (Filter.Eventually.of_forall hbound)
    convert hInt using 1
    funext t₁
    rw [hfactor t₁]
end OAI.AnalyticBridge
