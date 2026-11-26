-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49UniformDriverCountBoundV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:08:36.676947+00:00
-- url     : https://prove2.me/submissions/7b7612a0-0402-4237-921a-06191c6d0941

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49TruncatedWaitSLLNV4
import Theorems.Thm_Kyprianou_Ch04_exercise49CountLinearBoundV4
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_driver_interarrival_independent
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04 AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ w ∂P, ∃ N : ℕ, ∀ t ≥ 0,
      (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) t : ℝ) ≤ N + t / c := by
  have hident (n : ℕ) : IdentDistrib (τ n) (τ 0) P P :=
    ⟨(h.law_interarrival n).aemeasurable,(h.law_interarrival 0).aemeasurable,
      (h.law_interarrival n).map_eq.trans (h.law_interarrival 0).map_eq.symm⟩
  obtain ⟨c,hc,hlim⟩ := exercise49TruncatedWaitSLLNV4 P τ h.measurable_interarrival
    (avram_a06_original_compound_driver_interarrival_independent P τ Y h) hident
    (levy_foundations_compoundDriverInterarrivalPositive h (by norm_num))
  refine ⟨c,hc,?_⟩
  filter_upwards [hlim,avram_a06_original_cp_count_threshold_ae P τ Y h] with w hw hk
  obtain ⟨N,hN⟩ := hw
  exact ⟨N, exercise49CountLinearBoundV4 (fun n => τ n w)
    (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w)) c hc N hN hk⟩
