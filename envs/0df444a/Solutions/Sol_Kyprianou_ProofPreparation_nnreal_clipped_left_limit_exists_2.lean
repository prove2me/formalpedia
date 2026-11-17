-- Prove2me | solution 2 for Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:04:01.708568+00:00
-- url     : https://prove2.me/submissions/5d84e109-6761-4de4-9b7e-4f6b591844ef

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem nnreal_clipped_left_limit_exists
    (f : ℝ → ℝ)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => f (min (v : ℝ) 1))
        (𝓝[<] u) (𝓝 l) := by
  intro u hu
  by_cases h1 : (u : ℝ) ≤ 1
  · obtain ⟨l, hl⟩ := hL u ⟨by exact_mod_cast hu, h1⟩
    refine ⟨l, ?_⟩
    have hc : Tendsto (fun v : ℝ≥0 => (v : ℝ)) (𝓝[<] u) (𝓝[<] (u : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (NNReal.continuous_coe.tendsto u).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        exact NNReal.coe_lt_coe.2 hv
    refine (hl.comp hc).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have : (v : ℝ) ≤ 1 := (NNReal.coe_lt_coe.2 hv).le.trans h1
    simp [Function.comp, min_eq_left this]
  · rw [not_le] at h1
    refine ⟨f 1, ?_⟩
    apply tendsto_const_nhds.congr'
    have h1' : (1 : ℝ≥0) < u := by exact_mod_cast h1
    filter_upwards [Ioo_mem_nhdsLT h1'] with v hv
    have : (1 : ℝ) ≤ v := by exact_mod_cast hv.1.le
    simp [min_eq_right this]

end Kyprianou.ProofPreparation

theorem solution
    (f : ℝ → ℝ)
    (hL : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => f (min (v : ℝ) 1))
        (𝓝[<] u) (𝓝 l) := by
  first
  | exact Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists
  | exact Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists ..
  | (apply Kyprianou.ProofPreparation.nnreal_clipped_left_limit_exists <;> assumption)
