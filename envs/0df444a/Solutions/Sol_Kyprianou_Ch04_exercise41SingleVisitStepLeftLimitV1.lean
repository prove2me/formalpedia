-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SingleVisitStepLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:38:47.846653+00:00
-- url     : https://prove2.me/submissions/4d843b96-8698-4096-a09d-cd2a973aa8a7

import Mathlib
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution (s : NNReal) :
    ∀ t : NNReal, 0 < t →
      ∃ l : ℝ, Tendsto
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0)
        (nhdsWithin t (Iio t)) (nhds l) := by
  intro t ht
  by_cases h : s < t
  · refine ⟨1, ?_⟩
    have hc : Tendsto (fun _ : NNReal => (1 : ℝ))
        (𝓝[Iio t] t) (nhds (1 : ℝ)) := tendsto_const_nhds
    have hnear : ∀ᶠ u : NNReal in 𝓝[Iio t] t, s < u :=
      (eventually_gt_nhds h).filter_mono nhdsWithin_le_nhds
    exact hc.congr' (by
      filter_upwards [hnear] with u hu
      exact (if_pos hu.le).symm)
  · refine ⟨0, ?_⟩
    have hst : t ≤ s := le_of_not_gt h
    have hc : Tendsto (fun _ : NNReal => (0 : ℝ))
        (𝓝[Iio t] t) (nhds (0 : ℝ)) := tendsto_const_nhds
    exact hc.congr' (by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (if_neg (not_le.mpr (lt_of_lt_of_le hu hst))).symm)
