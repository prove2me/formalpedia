-- Prove2me | solution 1 for MeasureTheory.integral_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:10:38.156868+00:00
-- url     : https://prove2.me/submissions/848b1038-5cca-4aae-adc3-dd8728ebfa25

import Mathlib

-- carved verbatim out of submission 60e9c3d5-1ac3-4ae3-839d-92bea8b0af50, lines 178-186

section
set_option autoImplicit false
open MeasureTheory

theorem solution {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ℝ) (hπ : Integrable f π) (hρ : Integrable f ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ z, f z ∂(ENNReal.ofReal a • π + ENNReal.ofReal b • ρ)) =
      a * (∫ z, f z ∂π) + b * (∫ z, f z ∂ρ) := by
  rw [integral_add_measure (hπ.smul_measure ENNReal.ofReal_ne_top)
    (hρ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

end
