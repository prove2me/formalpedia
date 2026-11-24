-- Prove2me | solution 1 for LearnThenTest.uniform_bound_risk_control
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:29:42.212806+00:00
-- url     : https://prove2.me/submissions/a7f91660-aa7d-4192-a239-0d55c30a1a60

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter
open LearnThenTest

theorem solution {Ω L : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : L → ℝ) (Rplus : Ω → L → ℝ) (α δ : ℝ)
    (hRplus : ENNReal.ofReal (1 - δ) ≤ P {ω | ∀ l, R l ≤ Rplus ω l})
    (lhat : Ω → L) (hlhat : ∀ ω, Rplus ω (lhat ω) ≤ α) :
    IsRCP P R α δ lhat := by
  apply hRplus.trans
  apply measure_mono
  intro ω hw
  exact (hw (lhat ω)).trans (hlhat ω)
