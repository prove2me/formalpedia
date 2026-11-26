-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_tightness_ae_frequent_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:20:46.364504+00:00
-- url     : https://prove2.me/submissions/b6743eb1-e726-4a57-9b62-2d62081e8de0

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false

/-- Eventual uniform upper-tail bounds imply an almost surely finite frequent bound.
The events need not be measurable: continuity from below holds for outer measures. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : ℕ → Ω → ℝ)
    (hQ : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n in atTop, (P {w | C ≤ Q n w}).toReal ≤ η) :
    ∀ᵐ w ∂P, ∃ C : ℝ, ∃ᶠ n in atTop, Q n w < C := by
  let B : Set Ω := {w | ¬ ∃ C : ℝ, ∃ᶠ n in atTop, Q n w < C}
  apply ae_iff.mpr
  change P B = 0
  by_contra h
  have hpos : 0 < (P B).toReal :=
    ENNReal.toReal_pos h (measure_ne_top P B)
  obtain ⟨C,hC,hb⟩ := hQ ((P B).toReal/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  let S : ℕ → Set Ω := fun m => {w | ∀ n ≥ max m N, C ≤ Q n w}
  have hmono : Monotone S := by
    intro i j hij w hw n hn
    exact hw n ((max_le_max_right N hij).trans hn)
  have hsub : B ⊆ ⋃ m, S m := by
    intro w hw
    have hbad : ¬ (∃ᶠ n in atTop, Q n w < C) :=
      fun hc => hw ⟨C,hc⟩
    obtain ⟨m,hm⟩ := eventually_atTop.mp (not_frequently.mp hbad)
    exact mem_iUnion.mpr ⟨m,fun n hn => le_of_not_gt (hm n ((le_max_left _ _).trans hn))⟩
  have hS (m : ℕ) : P (S m) ≤ ENNReal.ofReal ((P B).toReal/2) := by
    apply (measure_mono (show S m ⊆ {w | C ≤ Q (max m N) w} from
      fun w hw => hw _ le_rfl)).trans
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hN _ (le_max_right _ _))
  have H : P B ≤ ENNReal.ofReal ((P B).toReal/2) := by
    apply (measure_mono hsub).trans
    rw [hmono.measure_iUnion]
    exact iSup_le hS
  have H' := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
  rw [ENNReal.toReal_ofReal (by positivity)] at H'
  linarith
