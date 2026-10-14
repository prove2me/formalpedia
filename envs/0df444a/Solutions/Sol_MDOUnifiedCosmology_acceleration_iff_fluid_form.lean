-- Prove2me | solution 1 for MDOUnifiedCosmology.acceleration_iff_fluid_form
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:37.990763+00:00
-- url     : https://prove2.me/submissions/711cf9a3-565d-44eb-acbb-a5b6eb81feef

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (κ : ℝ) (V : ℝ → ℝ) (a φ ρm pm : ℝ → ℝ) (t : ℝ) :
    AccelerationEq κ a φ ρm pm t ↔
      deriv (hubble a) t =
        -(κ ^ 2 / 2) * (rhoPhi κ V a φ t + pPhi κ V a φ t + ρm t + pm t) := by
  have hC : couplingFactor κ (φ t) ≠ 0 := ne_of_gt (by unfold couplingFactor; positivity)
  have hid : deriv (hubble a) t - (-(κ ^ 2 / 2) *
      (rhoPhi κ V a φ t + pPhi κ V a φ t + ρm t + pm t)) =
      (deriv (hubble a) t - (-(κ ^ 2 / 2) * couplingFactor κ (φ t) *
        (deriv φ t ^ 2 - 1 / 2 * (hubble a t * φ t * deriv φ t / couplingFactor κ (φ t) ^ 2)
          + ρm t + pm t))) / couplingFactor κ (φ t) := by
    unfold rhoPhi pPhi
    field_simp [hC]
    unfold couplingFactor
    ring
  unfold AccelerationEq
  constructor
  · intro h
    apply sub_eq_zero.mp
    rw [hid, sub_eq_zero.mpr h, zero_div]
  · intro h
    have hz := sub_eq_zero.mpr h
    rw [hid] at hz
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hC)


