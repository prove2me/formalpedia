-- Prove2me | solution 1 for MassEnergyEquivalence.rest_frame_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:29:15.617993+00:00
-- url     : https://prove2.me/submissions/30ad1a65-003c-42d4-ac05-2fc33201dbab

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- At zero velocity the Lorentz factor is one, momentum is zero,
and total energy equals the rest energy. -/
theorem solution (c m : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    relMomentum c m 0 = 0 ∧ relEnergy c m 0 = m * c ^ 2 := by
  simp [relMomentum, relEnergy, lorentzFactor]
