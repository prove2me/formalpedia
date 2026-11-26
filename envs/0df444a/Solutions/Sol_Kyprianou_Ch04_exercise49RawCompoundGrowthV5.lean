-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RawCompoundGrowthV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:10:44.351246+00:00
-- url     : https://prove2.me/submissions/2b0ff002-ff3d-415e-81a8-973db7563818

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_above_minus_one
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_ge_drift_minus_count
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
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (c : ℝ) (hc : 0 < c)
    (hCount : ∀ᵐ w ∂P, ∃ N : ℕ, ∀ t ≥ 0,
      (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) t : ℝ) ≤ N + t / c) :
    ∀ᵐ w ∂P, Tendsto (fun t : NNReal =>
      LevyFoundations.compoundPoisson (1 + 1 / c) τ Y (t : ℝ) w) atTop atTop := by
  filter_upwards [hCount,avram_a06_compound_driver_all_marks_above_minus_one h] with w hw hm
  obtain ⟨N,hN⟩ := hw
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (Real.toNNReal (B + (N : ℝ)))] with t ht
  have hR : B + (N : ℝ) ≤ (t : ℝ) := (Real.le_coe_toNNReal _).trans (by exact_mod_cast ht)
  have h1 := avram_a06_compoundPoisson_path_ge_drift_minus_count (1 + 1/c) τ Y w
    (fun n => (hm n).le) (t : ℝ)
  have h2 := hN (t : ℝ) t.coe_nonneg
  rw [add_mul,one_mul,one_div,mul_comm (c⁻¹),← div_eq_mul_inv] at h1
  rw [one_div]
  linarith
