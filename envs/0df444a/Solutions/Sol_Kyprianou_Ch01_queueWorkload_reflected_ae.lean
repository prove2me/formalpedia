-- Prove2me | solution 1 for Kyprianou.Ch01.queueWorkload_reflected_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:14:19.347142+00:00
-- url     : https://prove2.me/submissions/e3db8004-0fdf-42f0-baa4-fb9cbdfd40e0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_runningSup_bddAbove_ae
import Theorems.Thm_Kyprianou_Ch01_queueWorkload_reflected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Pointwise
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ (w : ℝ) (T : ℝ≥0),
      queueWorkload arrival claims w T ω =
        max (w - riskSurplus arrival claims 1 0 T ω)
          (sSup ({z : ℝ | ∃ s : ℝ≥0,
            s ≤ T ∧ z = riskSurplus arrival claims 1 0 s ω} -
            {riskSurplus arrival claims 1 0 T ω})) := by
  filter_upwards [riskSurplus_runningSup_bddAbove_ae
    P arrival claims rate F hd hr 1 0] with ω hω
  intro w T
  simpa using queueWorkload_reflected
    arrival claims w T ω (hω T)

