-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_frequent_grid_bound_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:06.060515+00:00
-- url     : https://prove2.me/submissions/625c6161-5751-4c53-a455-43170409e32a

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false

/-- An eventual uniform outer-probability tail bound bounds failure of a frequent grid bound. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℕ → Ω → ℝ) (C η : ℝ) (hη : 0 ≤ η)
    (hQ : ∀ᶠ n in atTop, (P {w | C ≤ Q n w}).toReal ≤ η) :
    (P {w | ¬ ∃ᶠ n in atTop, Q n w < C}).toReal ≤ η := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hQ
  let S : ℕ → Set Ω := fun m => {w | ∀ n ≥ max m N, C ≤ Q n w}
  have hmono : Monotone S := by
    intro i j hij w hw n hn
    exact hw n ((max_le_max_right N hij).trans hn)
  have hsub : {w | ¬ ∃ᶠ n in atTop, Q n w < C} ⊆ ⋃ m, S m := by
    intro w hw
    obtain ⟨m,hm⟩ := eventually_atTop.mp (not_frequently.mp hw)
    exact mem_iUnion.mpr ⟨m,fun n hn => le_of_not_gt (hm n ((le_max_left _ _).trans hn))⟩
  have hS (m : ℕ) : P (S m) ≤ ENNReal.ofReal η := by
    apply (measure_mono (show S m ⊆ {w | C ≤ Q (max m N) w} from
      fun w hw => hw _ le_rfl)).trans
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hN _ (le_max_right _ _))
  have H : P {w | ¬ ∃ᶠ n in atTop, Q n w < C} ≤ ENNReal.ofReal η := by
    apply (measure_mono hsub).trans
    rw [hmono.measure_iUnion]
    exact iSup_le hS
  simpa only [ENNReal.toReal_ofReal hη] using ENNReal.toReal_mono ENNReal.ofReal_ne_top H
