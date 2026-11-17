-- Prove2me | solution 1 for Kyprianou.ProofPreparation.nnreal_coe_tendsto_left
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:07.244857+00:00
-- url     : https://prove2.me/submissions/973c2f36-410a-4e60-a6fd-76829abb5ce6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem nnreal_coe_tendsto_left (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact NNReal.coe_lt_coe.2 hu

end Kyprianou.ProofPreparation

theorem solution (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
  first
  | exact Kyprianou.ProofPreparation.nnreal_coe_tendsto_left
  | exact Kyprianou.ProofPreparation.nnreal_coe_tendsto_left ..
  | (apply Kyprianou.ProofPreparation.nnreal_coe_tendsto_left <;> assumption)
