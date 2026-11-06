-- Prove2me | solution 1 for OAI.AnalyticBridge.double_weighted_fourier_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:14:36.298592+00:00
-- url     : https://prove2.me/submissions/3d24a735-8320-46bd-bf43-8a75e6b3a457

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_AnalyticBridge_weighted_fourier_minkowski
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
open OAI.AnalyticBridge
namespace OAI.AnalyticBridge
theorem _root_.solution
    {Ω : Type*} (S : Finset Ω)
    (b₁ b₂ : ℝ → ℂ) (φ : Ω → ℝ → ℝ → ℂ)
    (J₁ J₂ : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hinner : ∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ => b₂ t₂ * φ ω t₁ t₂) volume)
    (houter : ∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)) volume)
    (hweight₁ : Integrable
      (fun t₁ : ℝ => (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) volume)
    (hweight₂ : Integrable
      (fun t₂ : ℝ => (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) volume)
    (hφ : ∀ t₁ t₂ : ℝ,
      ‖∑ ω ∈ S, φ ω t₁ t₂‖ ≤
        H * (1 + ‖t₁‖) ^ J₁ * (1 + ‖t₂‖) ^ J₂) :
    ‖∑ ω ∈ S,
        ∫ t₁ : ℝ,
          b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
      H *
        (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
        (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) := by
  let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖
  have hI₂ : 0 ≤ I₂ :=
    integral_nonneg (fun t₂ => by positivity)
  have hinnerbound (t₁ : ℝ) :
      ‖∑ ω ∈ S, ∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂‖ ≤
        (H * (1 + ‖t₁‖) ^ J₁) * I₂ := by
    apply weighted_fourier_minkowski S b₂ (fun ω t₂ => φ ω t₁ t₂)
      J₂ (H * (1 + ‖t₁‖) ^ J₁) (by positivity)
      (hinner t₁) hweight₂
    intro t₂
    convert hφ t₁ t₂ using 1
  have houterbound :
      ‖∑ ω ∈ S,
          ∫ t₁ : ℝ,
            b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
        (H * I₂) *
          (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) := by
    apply weighted_fourier_minkowski S b₁
      (fun ω t₁ => ∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)
      J₁ (H * I₂) (mul_nonneg hH hI₂)
      houter hweight₁
    intro t₁
    convert hinnerbound t₁ using 1 ; ring
  simpa [I₂, mul_assoc, mul_comm, mul_left_comm] using houterbound
end OAI.AnalyticBridge
