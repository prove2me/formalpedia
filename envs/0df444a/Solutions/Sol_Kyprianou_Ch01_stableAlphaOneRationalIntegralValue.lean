-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneRationalIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:19:08.238323+00:00
-- url     : https://prove2.me/submissions/b9099100-240b-4d49-aca0-464903984797

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
set_option autoImplicit false
/-! The Laplace/Fubini partner of the index-one cosine integral has exact mass π/2. -/
theorem solution :
    (∫ t in Set.Ioi (0 : ℝ), (1 + t ^ 2)⁻¹) = Real.pi / 2 := by
  simpa using (integral_Ioi_inv_one_add_sq (i := (0 : ℝ)))
