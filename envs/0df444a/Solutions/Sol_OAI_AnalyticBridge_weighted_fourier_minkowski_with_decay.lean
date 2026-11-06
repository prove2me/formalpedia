-- Prove2me | solution 1 for OAI.AnalyticBridge.weighted_fourier_minkowski_with_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:11:41.320932+00:00
-- url     : https://prove2.me/submissions/e5a65d5f-8985-4050-85e8-98179b413c74

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_AnalyticBridge_weighted_fourier_minkowski

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
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ)
    (A J : ℕ) (R H C : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J)
    (hcoeff : (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C) :
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤ H * C := by
  have hM := weighted_fourier_minkowski S b φ J H hH hint hweight hφ
  calc
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤
        (1 + R) ^ A *
          (H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = H * ((1 + R) ^ A *
      ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hcoeff hH
end OAI.AnalyticBridge
