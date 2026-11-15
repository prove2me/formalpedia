-- Prove2me | solution 1 for Kyprianou.Ch01.queueWorkload_nonneg_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:10:05.107553+00:00
-- url     : https://prove2.me/submissions/2cf27a6e-beee-460f-a439-edb7c5f7978b

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_runningSup_bddAbove_ae
import Theorems.Thm_Kyprianou_Ch01_queueWorkload_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ (w : ℝ) (T : ℝ≥0),
      0 ≤ queueWorkload arrival claims w T ω := by
  filter_upwards [riskSurplus_runningSup_bddAbove_ae
    P arrival claims rate F hd hr 1 0] with ω hω
  intro w T
  exact queueWorkload_nonneg arrival claims w T ω (hω T)
