-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_energy_markov_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:05:17.500053+00:00
-- url     : https://prove2.me/submissions/72b05178-9115-4b05-bb63-f97d1c3447ef

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
/-- A nonnegative integrable variable with bounded mean has a uniform Markov tail. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hFi : Integrable F P) (hF0 : ∀ w, 0 ≤ F w)
    (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η)
    (hmean : (∫ w, F w ∂P) ≤ K) :
    (P {w | 2*K/η+1 ≤ F w}).toReal ≤ η/2 := by
  let D := 2*K/η+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all P hF0) hFi D
  change D*(P {w | D ≤ F w}).toReal ≤ _ at hmark
  have hprod : K ≤ D*(η/2) := by dsimp [D]; field_simp; nlinarith
  change (P {w | D ≤ F w}).toReal ≤ η/2
  apply (le_of_mul_le_mul_left _ hD)
  linarith
