-- Prove2me | solution 1 for MDOUnifiedCosmology.energy_density_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:29.643486+00:00
-- url     : https://prove2.me/submissions/9ef094f4-7a9f-45c5-bbea-501717599777

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (κ : ℝ) (V : ℝ → ℝ) (a φ ρm : ℝ → ℝ) (t : ℝ)
    (h5 : FriedmannEq κ V a φ ρm t) :
    rhoPhi κ V a φ t = κ ^ 2 * φ t ^ 2 / 8 * ρm t
      + couplingFactor κ (φ t) * (deriv φ t ^ 2 / 2 + V (φ t)) := by
  have hC : couplingFactor κ (φ t) ≠ 0 := ne_of_gt (by unfold couplingFactor; positivity)
  unfold rhoPhi
  rw [show hubble a t ^ 2 = _ from h5]
  field_simp [hC]
  unfold couplingFactor
  ring


