-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_power_interval_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:26:31.74618+00:00
-- url     : https://prove2.me/submissions/68b52e71-2bd1-47df-80ac-d43e14aef15a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_weighted_integrable
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) (hx : 0 ≤ x) :
    ∀ n : ℕ, IntervalIntegrable (scaleConvolutionPower (W 0) n)
      volume 0 x := by
  intro n
  let β : ℝ := max 0 (Phi ψ 0) + 1
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith [le_max_left (0 : ℝ) (Phi ψ 0)]
  have hroot : Phi ψ 0 < β := by
    dsimp [β]
    linarith [le_max_right (0 : ℝ) (Phi ψ 0)]
  have hw := (source_scale_power_weighted_integrable ψ W hW β hβ hroot) n
  have hsub : Set.Ioc (0 : ℝ) x ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    exact hs.1
  have hwlocal : IntervalIntegrable
      (fun t : ℝ => Real.exp (-β * t) * scaleConvolutionPower (W 0) n t)
      volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 (hw.mono_set hsub)
  have hc : ContinuousOn (fun t : ℝ => Real.exp (β * t))
      (Set.uIcc (0 : ℝ) x) := by fun_prop
  have hp := hwlocal.mul_continuousOn hc
  convert hp using 1
  ext t
  have he : Real.exp (-β * t) * Real.exp (β * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    scaleConvolutionPower (W 0) n t =
        (Real.exp (-β * t) * Real.exp (β * t)) *
          scaleConvolutionPower (W 0) n t := by rw [he]; ring
    _ = (Real.exp (-β * t) * scaleConvolutionPower (W 0) n t) *
          Real.exp (β * t) := by ring
