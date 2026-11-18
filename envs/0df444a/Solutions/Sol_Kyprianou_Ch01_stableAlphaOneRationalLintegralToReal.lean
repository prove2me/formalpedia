-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneRationalLintegralToReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:37:17.37385+00:00
-- url     : https://prove2.me/submissions/896afadb-998f-4197-9be6-ddcd7b404c7a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! Exact original-typed nonnegative integral conversion. -/
theorem solution :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal ((1 + a ^ 2)⁻¹)).toReal =
    (∫ a in Ioi (0 : ℝ), (1 + a ^ 2)⁻¹) := by
  have hi : IntegrableOn (fun a : ℝ => (1 + a ^ 2)⁻¹)
      (Ioi (0 : ℝ)) := integrable_inv_one_add_sq.integrableOn
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun a : ℝ => (1 + a ^ 2)⁻¹) := by
    filter_upwards [] with a
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun a => inv_nonneg.mpr (by positivity))
