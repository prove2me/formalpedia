-- Prove2me | solution 1 for MDOUnifiedCosmology.friedmann_iff_fluid_form
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:36.325826+00:00
-- url     : https://prove2.me/submissions/5f0ac02f-36d3-4814-9d01-be3e549855bc

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (κ : ℝ) (V : ℝ → ℝ) (a φ ρm : ℝ → ℝ) (t : ℝ) :
    FriedmannEq κ V a φ ρm t ↔
      hubble a t ^ 2 = κ ^ 2 / 3 * (rhoPhi κ V a φ t + ρm t) := by
  have hC : couplingFactor κ (φ t) ≠ 0 := ne_of_gt (by unfold couplingFactor; positivity)
  have hid : hubble a t ^ 2 - κ ^ 2 / 3 * (rhoPhi κ V a φ t + ρm t) =
      (hubble a t ^ 2 - κ ^ 2 / 3 * couplingFactor κ (φ t) *
        (deriv φ t ^ 2 / 2 + V (φ t) + ρm t)) / couplingFactor κ (φ t) := by
    unfold rhoPhi
    field_simp [hC]
    unfold couplingFactor
    ring
  unfold FriedmannEq
  constructor
  · intro h
    apply sub_eq_zero.mp
    rw [hid, sub_eq_zero.mpr h, zero_div]
  · intro h
    have hz := sub_eq_zero.mpr h
    rw [hid] at hz
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hC)


