-- Prove2me | solution 1 for Kyprianou.Ch01.riskSurplus_increment_indep_stationary
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T10:07:13.513938+00:00
-- url     : https://prove2.me/submissions/1a0e2030-2fe6-4ed0-b062-6e5a35cb5e14

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_indep
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_stationary

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators

set_option autoImplicit false

/-- Reduction of riskSurplus_increment_indep_stationary to independent increments
and stationary increments of the Cramér–Lundberg surplus process. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (premium : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
        (MeasurableSpace.comap
          (fun ω => riskSurplus arrival claims premium 0 t ω -
            riskSurplus arrival claims premium 0 s ω) inferInstance)
        (naturalSigma (riskSurplus arrival claims premium 0) s) P ∧
      P.map (fun ω => riskSurplus arrival claims premium 0 t ω -
          riskSurplus arrival claims premium 0 s ω) =
        P.map (riskSurplus arrival claims premium 0 (t - s)) := by
  constructor
  · exact Kyprianou.Ch01.riskSurplus_increment_indep
      P arrival claims rate hrate F hDriver premium s t hst
  · exact Kyprianou.Ch01.riskSurplus_increment_stationary
      P arrival claims rate hrate F hDriver premium s t hst
