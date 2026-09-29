-- Prove2me | solution 1 for HorizontalPadicL.not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-21T09:21:16.800799+00:00
-- url     : https://prove2.me/submissions/dff639fd-7e6b-4169-b1ea-fff650f41f09

import Theorems.Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
import Theorems.Thm_HorizontalPadicL_localEulerFactorDegreeTwo_iff_not_degreeBelowTwo

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := by
  rw [localEulerFactorDegreeTwo_iff_not_degreeBelowTwo E p hp]
  exact not_congr
    (minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo E hmod p hp)
