-- Prove2me | solution 1 for MassEnergyEquivalence.massless_energy_eq_pc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:42:42.388123+00:00
-- url     : https://prove2.me/submissions/92d5c02a-46f9-4754-9ce6-9f75863bbd5c

import Mathlib.Tactic.Linarith
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- Nonnegative massless energy and momentum satisfy E = pc. -/
theorem solution (c E p : ℝ) (hc : 0 < c) (hE : 0 ≤ E) (hp : 0 ≤ p)
    (h : E ^ 2 - (p * c) ^ 2 = ((0 : ℝ) * c ^ 2) ^ 2) :
    E = p * c := by
  have hpc : 0 ≤ p * c := mul_nonneg hp (le_of_lt hc)
  have hs : E ^ 2 = (p * c) ^ 2 := by
    nlinarith [h]
  nlinarith [sq_nonneg (E - p * c)]
