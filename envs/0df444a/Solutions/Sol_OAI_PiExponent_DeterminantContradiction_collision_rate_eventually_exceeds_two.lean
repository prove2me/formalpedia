-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collision_rate_eventually_exceeds_two
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:01:25.916698+00:00
-- url     : https://prove2.me/submissions/45b5815f-cfee-4fa0-ab1f-1f1fc152863f

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collisionRate_tendsto_collisionLimit
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop, 2 < collisionRate d H := by
  have hlimit : Tendsto (fun H : Real => collisionRate d H) atTop
      (nhds (collisionLimit d)) :=
    OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_collisionLimit nu d
  have hmargin : 2 < collisionLimit d := d.collision_margin
  filter_upwards [hlimit.eventually (Ioi_mem_nhds hmargin)] with H hH
  exact hH