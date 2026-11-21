-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_power_nonnegative_all_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:14:45.511437+00:00
-- url     : https://prove2.me/submissions/bb6ae61b-8a4e-4a37-baba-4a07422cc890

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ (n : ℕ) (x : ℝ),
      0 ≤ scaleConvolutionPower (W 0) n x := by
  have hpos := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).1
  intro n
  induction n with
  | zero =>
      intro x
      simpa only [scaleConvolutionPower] using hpos x
  | succ n ih =>
      intro x
      change 0 ≤ ∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * scaleConvolutionPower (W 0) n (x - s) ∂volume
      apply integral_nonneg_of_ae
      filter_upwards [] with s
      exact mul_nonneg (hpos s) (ih (x - s))
