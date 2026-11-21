-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_weighted_series_terms_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:17:58.111242+00:00
-- url     : https://prove2.me/submissions/48475a4f-6788-477b-80fc-3bfd0ae20cdc

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) :
    ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x))
      (Set.Ioi (0 : ℝ)) volume := by
  intro n
  have hh := (source_scale_power_weighted_integrable ψ W hW θ hθ hroot0) n
  have hi : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * scaleConvolutionPower (W 0) n x)
      (Set.Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using hh
  have heq : (fun x : ℝ => Real.exp (-(θ * x)) *
      (q ^ n * scaleConvolutionPower (W 0) n x)) =
      (fun x : ℝ => q ^ n *
        (Real.exp (-(θ * x)) * scaleConvolutionPower (W 0) n x)) := by
    funext x
    ring
  rw [heq]
  exact hi.const_mul _
