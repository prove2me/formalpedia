-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:48:48.700004+00:00
-- url     : https://prove2.me/submissions/6619b3d7-4db3-4fe5-a121-ff4e934e4b17

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseNearZeroIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseAwayZeroIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false

theorem solution :
    ∀ z : ℝ, 0 < z →
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  intro z hz
  let delta : ℝ := 1 / (1 + z)
  have hd : 0 < delta := by
    dsimp [delta]
    positivity
  have hNear :=
    Kyprianou.Ch01.stableAlphaOneLogPhaseNearZeroIntegrable z hz
  have hNearClosed :
      IntegrableOn (fun r : ℝ =>
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
        (Ioc (0 : ℝ) delta) := by
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).2 (by simpa [delta] using hNear)
  have hAway :=
    Kyprianou.Ch01.stableAlphaOneLogPhaseAwayZeroIntegrable z delta hz hd
  have hBoth := hNearClosed.union hAway
  simpa only [Ioc_union_Ioi_eq_Ioi (le_of_lt hd)] using hBoth
