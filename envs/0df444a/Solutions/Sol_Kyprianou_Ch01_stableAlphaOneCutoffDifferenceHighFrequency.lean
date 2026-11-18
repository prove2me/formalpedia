-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCutoffDifferenceHighFrequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:56:22.456063+00:00
-- url     : https://prove2.me/submissions/92dd1fa6-f213-4b4d-af0e-50391325d732

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! The difference of stable Lévy compensation cutoffs is exactly 1/u on [1,z). -/
theorem solution
    (z u : ℝ) (hz : 1 ≤ z) :
    ((if u < z then (1 : ℝ) else 0) -
      (if u < 1 then (1 : ℝ) else 0)) / u =
        (Set.Ico (1 : ℝ) z).indicator (fun x : ℝ => x⁻¹) u := by
  by_cases hlt : u < 1
  · have huz : u < z := lt_of_lt_of_le hlt hz
    have hnot : u ∉ Ico (1 : ℝ) z := fun h => not_le.mpr hlt h.1
    simp [hlt, huz, hnot]
  · by_cases huz : u < z
    · have hmem : u ∈ Ico (1 : ℝ) z := ⟨le_of_not_gt hlt, huz⟩
      simp [hlt, huz, hmem, one_div]
    · have hnot : u ∉ Ico (1 : ℝ) z := fun h => huz h.2
      simp [hlt, huz, hnot]
