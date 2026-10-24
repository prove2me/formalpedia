-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:50:04.09806+00:00
-- url     : https://prove2.me/submissions/530742f6-ff42-4073-b305-ef7f8752bbb2

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
open Filter Topology

theorem solution
    (lower upper f : Real → Real) (L : Real)
    (hlower : Tendsto lower atTop (nhds L))
    (hupper : Tendsto upper atTop (nhds L))
    (hbound : Filter.Eventually
      (fun x : Real => And (lower x ≤ f x) (f x ≤ upper x)) atTop) :
    Tendsto f atTop (nhds L) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [hbound] with x hx
    exact hx.1
  · filter_upwards [hbound] with x hx
    exact hx.2