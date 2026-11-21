-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_discount_series_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:25:51.056181+00:00
-- url     : https://prove2.me/submissions/012de703-d576-48a7-944d-5f2ff46df832

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_compact_positive
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n x)
      (Set.Ioi (0 : ℝ)) := by
  apply continuousOn_of_locally_continuousOn
  intro x hx
  change 0 < x at hx
  refine ⟨Set.Ioo (x / 2) (x + 1), isOpen_Ioo, ?_, ?_⟩
  · exact ⟨by linarith, by linarith⟩
  · have hcomp := source_scale_discount_series_compact_positive
      ψ W hW q (x / 2) (x + 1) hq (by linarith) (by linarith)
    apply hcomp.mono
    intro y hy
    exact ⟨hy.2.1.le, hy.2.2.le⟩
