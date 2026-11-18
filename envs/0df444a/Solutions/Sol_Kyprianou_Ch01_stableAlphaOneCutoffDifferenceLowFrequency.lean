-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCutoffDifferenceLowFrequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:57:12.409446+00:00
-- url     : https://prove2.me/submissions/ce98254f-35be-4fd7-a712-71833581ee88

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! For 0<z≤1 the cutoff difference is minus 1/u on the interval [z,1). -/
theorem solution
    (z u : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    ((if u < z then (1 : ℝ) else 0) -
      (if u < 1 then (1 : ℝ) else 0)) / u =
        -((Set.Ico z (1 : ℝ)).indicator (fun x : ℝ => x⁻¹) u) := by
  by_cases hlt : u < z
  · have hu1 : u < 1 := lt_of_lt_of_le hlt hz1
    have hnot : u ∉ Ico z (1 : ℝ) := fun h => not_le.mpr hlt h.1
    simp [hlt, hu1, hnot]
  · by_cases hu1 : u < 1
    · have hmem : u ∈ Ico z (1 : ℝ) := ⟨le_of_not_gt hlt, hu1⟩
      simp [hlt, hu1, hmem, div_eq_mul_inv]
    · have hnot : u ∉ Ico z (1 : ℝ) := fun h => hu1 h.2
      simp [hlt, hu1, hnot]
