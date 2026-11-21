-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_discount_series_positive_x
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:18:10.345155+00:00
-- url     : https://prove2.me/submissions/5194d547-ad9a-4948-b421-939a803cce2e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_real_positive_x
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_summable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    ((W q x : ℝ) : ℂ) =
      ∑' n : ℕ, (q : ℂ) ^ n *
        ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ) := by
  have hreal := source_scale_discount_series_real_positive_x ψ W hW x q hx hq
  have hint := source_scale_all_power_local_integrability ψ W hW
  have hs := source_scale_discount_series_summable ψ W hW hint x q hx.le hq
  rw [hreal]
  calc
    (((∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) : ℝ) : ℂ) =
       ∑' n : ℕ, (((q ^ n * scaleConvolutionPower (W 0) n x) : ℝ) : ℂ) :=
      Complex.ofReal_tsum _
    _ = ∑' n : ℕ, (q : ℂ) ^ n *
        ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ) := by
      congr 1
      ext n
      simp only [Complex.ofReal_mul, Complex.ofReal_pow]
