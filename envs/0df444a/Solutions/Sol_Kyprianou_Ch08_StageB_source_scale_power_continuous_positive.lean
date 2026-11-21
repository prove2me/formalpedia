-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_power_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:25:34.446026+00:00
-- url     : https://prove2.me/submissions/9ecd517a-a9fd-4147-8ccb-4825d8824852

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_of_weighted_integrable
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ n : ℕ, ContinuousOn (scaleConvolutionPower (W 0) n)
      (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (W 0) (Set.Ici (0 : ℝ)) :=
    (source_family_positive_monotone ψ W hW 0 (le_refl (0 : ℝ))).2.2
  let β : ℝ := max 0 (Phi ψ 0) + 1
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith [le_max_left (0 : ℝ) (Phi ψ 0)]
  have hroot : Phi ψ 0 < β := by
    dsimp [β]
    linarith [le_max_right (0 : ℝ) (Phi ψ 0)]
  intro n
  cases n with
  | zero =>
      simpa only [scaleConvolutionPower] using
        (hcont.mono (by intro x hx; change 0 < x at hx; exact hx.le))
  | succ n =>
      have hint := (source_scale_power_weighted_integrable ψ W hW β hβ hroot) n
      have hconv := AvramDividend.Classical.positive_causal_convolution_continuous_of_weighted_integrable
        (W 0) (scaleConvolutionPower (W 0) n) β hcont
        (by simpa only [neg_mul] using hint)
      simpa only [scaleConvolutionPower] using hconv
