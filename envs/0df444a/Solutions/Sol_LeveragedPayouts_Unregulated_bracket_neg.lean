-- Prove2me | solution 1 for LeveragedPayouts.Unregulated.bracket_neg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:52:46.253343+00:00
-- url     : https://prove2.me/submissions/455db645-91b5-483e-a78f-c6ba3314a6d3

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

set_option autoImplicit false
open Filter Topology LeveragedPayouts.Unregulated

theorem solution (E : Economy) (ρ lρ e : ℝ) (hlρ : IsFirstBestLabor E ρ lρ) (he : e < E.π) :
    (e - e ^ 2 / (2 * E.π)) * deriv E.f lρ / E.R - ρ * deriv E.g (1 - lρ) < 0 := by
  obtain ⟨hl0, hl1, heq⟩ := hlρ
  have hRpos : 0 < E.R := by linarith [E.hR]
  have hπ := E.hπ0
  have hF : 0 < deriv E.f lρ := E.hf.2.2.2.1 lρ hl0
  rw [← heq]
  have key : (e - e ^ 2 / (2 * E.π)) * deriv E.f lρ / E.R - E.π * deriv E.f lρ / (2 * E.R)
      = -(deriv E.f lρ * (E.π - e) ^ 2 / (2 * E.π * E.R)) := by
    field_simp
    ring
  rw [key]
  have : 0 < deriv E.f lρ * (E.π - e) ^ 2 / (2 * E.π * E.R) := by
    apply div_pos
    · exact mul_pos hF (pow_pos (by linarith) 2)
    · positivity
  linarith
