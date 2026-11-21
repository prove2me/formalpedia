-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_series_laplace_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:14:01.084427+00:00
-- url     : https://prove2.me/submissions/149fdf4e-441c-4363-af2f-57f593e319ba

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_weighted_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_weighted_laplace
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ Phi ψ q < θ ∧
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ * x)) *
          (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x))
        (Set.Ioi (0 : ℝ)) volume ∧
      (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
        (ψ θ - q)⁻¹ := by
  refine ⟨max 0 (max (Phi ψ 0) (Phi ψ q)) + 1, ?_⟩
  intro θ hθ
  have hz : 0 ≤ θ := by
    linarith [le_max_left (0 : ℝ) (max (Phi ψ 0) (Phi ψ q))]
  have hroot0 : Phi ψ 0 < θ := by
    linarith [le_max_left (Phi ψ 0) (Phi ψ q),
      le_max_right (0 : ℝ) (max (Phi ψ 0) (Phi ψ q))]
  have hrootq : Phi ψ q < θ := by
    linarith [le_max_right (Phi ψ 0) (Phi ψ q),
      le_max_right (0 : ℝ) (max (Phi ψ 0) (Phi ψ q))]
  exact ⟨hz,hrootq,
    source_real_discount_series_weighted_integrable ψ W hW q θ hq hz hroot0 hrootq,
    source_real_discount_series_weighted_laplace ψ W hW q θ hq hz hroot0 hrootq⟩
