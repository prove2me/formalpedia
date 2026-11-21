-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_power_laplace_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:08:22.279449+00:00
-- url     : https://prove2.me/submissions/5e10f8d1-4d0c-4e6e-814f-786830cd0f9d

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_laplace_geometric
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (β : ℝ)
    (hβ : 0 ≤ β) (hroot : Phi ψ 0 < β) :
    ∀ n : ℕ, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-β * t) * scaleConvolutionPower (W 0) n t ∂volume) =
      ((ψ β)⁻¹) ^ (n + 1) := by
  have hscale := hW 0 (le_refl (0 : ℝ))
  have hsource := hscale.2.2.2.2.2 β hβ hroot
  have hFn := source_scale_power_weighted_integrable ψ W hW β hβ hroot
  have hFn' : ∀ n : ℕ, IntegrableOn (fun t : ℝ =>
      Real.exp (-(β * t)) * scaleConvolutionPower (W 0) n t)
      (Set.Ioi (0 : ℝ)) volume := by
    intro n
    simpa only [neg_mul] using hFn n
  have hκmass : (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(β * t)) * W 0 t ∂volume) = (ψ β)⁻¹ := by
    simpa using hsource.2
  have hresult := AvramDividend.Classical.causal_convolution_powers_laplace_geometric
    (W 0) (scaleConvolutionPower (W 0)) β ((ψ β)⁻¹)
    (by simpa only [neg_mul] using hsource.1) hFn' rfl (fun n => rfl) hκmass
  intro n
  simpa only [neg_mul] using hresult n
