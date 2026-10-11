-- Prove2me | solution 1 for MassEnergyEquivalence.parker_probe_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:55:41.650592+00:00
-- url     : https://prove2.me/submissions/9101c7cf-52a5-42ec-b0a7-b29cba868a98

import Mathlib.Tactic.NormNum
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- Exact verification of the two-sided error tolerance by rational arithmetic. -/
theorem solution :
    |3 * (68600 : ℝ) ^ 2 / (4 * (299792458 : ℝ) ^ 2) - 3.9e-8| < 0.05e-8 := by
  rw [abs_lt]
  constructor <;> norm_num
