-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SingleVisitStepRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:40:16.514625+00:00
-- url     : https://prove2.me/submissions/6cf58e61-a5bb-4c3d-a92f-40fee52f33bb

import Mathlib
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution (s : NNReal) :
    ∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0) (Ici t) t := by
  intro t
  change Tendsto (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0)
    (𝓝[Ici t] t) (nhds (if s ≤ t then (1 : ℝ) else 0))
  by_cases h : s ≤ t
  · have he : ∀ᶠ u : NNReal in 𝓝[Ici t] t, s ≤ u :=
      by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact h.trans hu
    have hconst : Tendsto (fun _ : NNReal => (1 : ℝ))
        (𝓝[Ici t] t) (nhds (1 : ℝ)) := tendsto_const_nhds
    simpa only [if_pos h] using hconst.congr' (by
      filter_upwards [he] with u hu
      exact (if_pos hu).symm)
  · have hlt : t < s := lt_of_not_ge h
    have he : ∀ᶠ u : NNReal in 𝓝[Ici t] t, u < s :=
      (eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : NNReal => (0 : ℝ))
        (𝓝[Ici t] t) (nhds (0 : ℝ)) := tendsto_const_nhds
    simpa only [if_neg h] using hconst.congr' (by
      filter_upwards [he] with u hu
      exact (if_neg (not_le.mpr hu)).symm)
