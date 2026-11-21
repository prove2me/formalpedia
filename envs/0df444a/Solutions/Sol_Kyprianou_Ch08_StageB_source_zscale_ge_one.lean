-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_zscale_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:36:50.192468+00:00
-- url     : https://prove2.me/submissions/616ad780-d63d-4dd5-aff0-e6fa68f4fb6f

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    1 ≤ Zscale q (W q) x := by
  have hpos : ∀ y : ℝ, 0 ≤ W q y :=
    (source_family_positive_monotone ψ W hW q hq).1
  have hint : 0 ≤ ∫ y in (0 : ℝ)..x, W q y := by
    apply intervalIntegral.integral_nonneg hx
    intro y hy
    exact hpos y
  dsimp [Zscale]
  nlinarith [mul_nonneg hq hint]
