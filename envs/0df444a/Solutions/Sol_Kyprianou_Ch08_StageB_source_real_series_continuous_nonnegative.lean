-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_series_continuous_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:22:36.570041+00:00
-- url     : https://prove2.me/submissions/6416b50a-b0ee-4655-84b9-7e32c7738e97

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_continuous
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n x) (Set.Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x →
      0 ≤ (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x)) := by
  exact ⟨source_real_discount_series_continuous ψ W hW q hq,
    fun x _ => source_real_discount_series_nonnegative ψ W hW q hq x⟩
