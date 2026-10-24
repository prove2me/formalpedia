-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_collisionLimit
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:20:42.348991+00:00
-- url     : https://prove2.me/submissions/f95f3544-a063-47c2-89d6-d01cc87a7457

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collisionRate_tendsto_from_counts
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_normalized_tendsto
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_lowIndexCount_normalized_tendsto
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu) :
    Tendsto (fun H : Real => collisionRate d H) atTop (nhds (collisionLimit d)) := by
  apply OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_from_counts nu d
  all_goals first
    | exact OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto nu d
    | exact OAI.PiExponent.DeterminantContradiction.lowIndexCount_normalized_tendsto nu d
