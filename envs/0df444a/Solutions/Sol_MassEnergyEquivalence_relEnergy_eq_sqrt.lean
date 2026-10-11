-- Prove2me | solution 1 for MassEnergyEquivalence.relEnergy_eq_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:37:59.993971+00:00
-- url     : https://prove2.me/submissions/b695c76e-747d-49e6-a466-5a154bcabdb5

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs
import Theorems.Thm_MassEnergyEquivalence_energy_momentum_relation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- The positive square-root energy formula follows from the
energy-momentum identity and nonnegativity of relativistic energy. -/
theorem solution (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m)
    (hv : ‖v‖ < c) :
    relEnergy c m v =
      Real.sqrt ((m * c ^ 2) ^ 2 + (‖relMomentum c m v‖ * c) ^ 2) := by
  have hEn : 0 ≤ relEnergy c m v := by
    unfold relEnergy lorentzFactor
    positivity
  have hrel := MassEnergyEquivalence.energy_momentum_relation c m v hc hm hv
  have heq :
      (relEnergy c m v) ^ 2 =
      (m * c ^ 2) ^ 2 + (‖relMomentum c m v‖ * c) ^ 2 := by
    nlinarith [hrel]
  calc
    relEnergy c m v = Real.sqrt ((relEnergy c m v) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hEn]
    _ = Real.sqrt ((m * c ^ 2) ^ 2 +
        (‖relMomentum c m v‖ * c) ^ 2) := by rw [heq]
