-- Prove2me | solution 1 for MDOUnifiedCosmology.pressure_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:31.270959+00:00
-- url     : https://prove2.me/submissions/9c814754-672a-41f2-a2aa-3bf92c8bb1b1

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (κ : ℝ) (V : ℝ → ℝ) (a φ ρm pm : ℝ → ℝ) (t : ℝ)
    (h5 : FriedmannEq κ V a φ ρm t) (h6 : AccelerationEq κ a φ ρm pm t) :
    pPhi κ V a φ t = κ ^ 2 * φ t ^ 2 / 8 * pm t
      + couplingFactor κ (φ t) * (deriv φ t ^ 2 / 2 - V (φ t))
      - 1 / 2 * (hubble a t * φ t * deriv φ t / couplingFactor κ (φ t)) := by
  have hC : couplingFactor κ (φ t) ≠ 0 := ne_of_gt (by unfold couplingFactor; positivity)
  unfold pPhi
  rw [show hubble a t ^ 2 = _ from h5, show deriv (hubble a) t = _ from h6]
  field_simp [hC]
  unfold couplingFactor
  ring


