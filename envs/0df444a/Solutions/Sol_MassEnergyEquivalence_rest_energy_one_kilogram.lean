-- Prove2me | solution 1 for MassEnergyEquivalence.rest_energy_one_kilogram
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:29:58.952186+00:00
-- url     : https://prove2.me/submissions/67c178e6-ccfd-4f6d-b8a9-d47fc1a28423

import Mathlib.Tactic.NormNum
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- The rest energy of a mass of one kilogram expressed in joules. -/
theorem solution :
    restEnergy 299792458 1 = 89875517873681764 := by
  norm_num [restEnergy]
