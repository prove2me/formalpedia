-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_rightcont_weight_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:14:49.080653+00:00
-- url     : https://prove2.me/submissions/7c09dfe1-5791-4eb0-8907-068f7231ee39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The right-continuous filtration supports arbitrary measurable stopped-history weights. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (τ : Ω → NNReal)
    (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {w : Ω | τ w ≤ s})
    (W : Ω → ℝ≥0∞) (hW : Measurable W)
    (hPast : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] W)
    (R : (NNReal → ℝ) → ℝ≥0∞) (hR : Measurable R) :
    (∫⁻ w, W w * R (fun t => L.X (τ w + t) w - L.X (τ w) w) ∂P) =
      (∫⁻ w, W w ∂P) * (∫⁻ w, R (fun t => L.X t w) ∂P) := by
  obtain ⟨Y,hY,_,_,_⟩ := levy_rightCont_process L
  have h := levy_finiteStopping_historyWeight_futureReward_factor Y τ hτ W hW hPast R hR
  simpa only [hY] using h
