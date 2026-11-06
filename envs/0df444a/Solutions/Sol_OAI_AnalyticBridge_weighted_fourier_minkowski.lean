-- Prove2me | solution 1 for OAI.AnalyticBridge.weighted_fourier_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:45.066677+00:00
-- url     : https://prove2.me/submissions/faa2f9ea-67fd-4190-b085-310c8496a28e

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization

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
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ) (J : ℕ) (H : ℝ)
    (_hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J) :
    ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤
      H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hR : Integrable
      (fun t : ℝ => H * ((1 + ‖t‖) ^ J * ‖b t‖)) volume :=
    hweight.const_mul H
  calc
    ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ =
        ‖∫ t : ℝ, ∑ ω ∈ S, b t * φ ω t‖ := by
      rw [integral_finsetSum S hint]
    _ ≤ ∫ t : ℝ, ‖∑ ω ∈ S, b t * φ ω t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, H * ((1 + ‖t‖) ^ J * ‖b t‖) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (by intro t; positivity))
        hR
      filter_upwards [] with t
      rw [← Finset.mul_sum, norm_mul]
      calc
        ‖b t‖ * ‖∑ ω ∈ S, φ ω t‖ ≤
            ‖b t‖ * (H * (1 + ‖t‖) ^ J) :=
          mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = H * ((1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ = H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
      rw [integral_const_mul]
end OAI.AnalyticBridge
