-- Prove2me | solution 1 for GoldenRatioVI.Fixed.fejer_converges
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:39:47.690594+00:00
-- url     : https://prove2.me/submissions/e30e49b9-59f6-4f3d-8c89-edf88131b55a

import Mathlib

open Filter

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z : ℕ → E) (C : Set E) (hC : C.Nonempty)
    (hfejer : ∀ k : ℕ, ∀ c ∈ C, ‖z (k + 1) - c‖ ≤ ‖z k - c‖)
    (hclust : ∀ x : E, MapClusterPt x Filter.atTop z → x ∈ C) :
    ∃ x ∈ C, Filter.Tendsto z Filter.atTop (nhds x) := by
  obtain ⟨c₀, hc₀⟩ := hC
  -- Fejér monotonicity makes every distance `‖z k − c‖`, `c ∈ C`, nonincreasing in `k`
  have hanti : ∀ c ∈ C, ∀ j k : ℕ, j ≤ k → ‖z k - c‖ ≤ ‖z j - c‖ := by
    intro c hc j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hfejer n c hc).trans ih
  have hbd : ∀ k, ‖z k - c₀‖ ≤ ‖z 0 - c₀‖ := fun k => hanti c₀ hc₀ 0 k (Nat.zero_le k)
  -- hence the sequence is bounded, and in finite dimensions has a cluster point
  have hsub : Set.range z ⊆ Metric.closedBall c₀ ‖z 0 - c₀‖ := by
    rintro w ⟨k, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hbd k
  have hcpt : IsCompact (Metric.closedBall c₀ ‖z 0 - c₀‖) := isCompact_closedBall c₀ _
  have hle : Filter.map z Filter.atTop ≤ Filter.principal (Metric.closedBall c₀ ‖z 0 - c₀‖) := by
    refine Filter.le_principal_iff.mpr (Filter.mem_map.mpr ?_)
    exact Filter.Eventually.of_forall fun k => hsub ⟨k, rfl⟩
  obtain ⟨x, -, hxcl⟩ := hcpt.exists_clusterPt hle
  have hxC : x ∈ C := hclust x hxcl
  refine ⟨x, hxC, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfreq : ∃ᶠ k in Filter.atTop, z k ∈ Metric.ball x ε :=
    mapClusterPt_iff_frequently.mp hxcl _ (Metric.ball_mem_nhds x hε)
  obtain ⟨N, -, hNb⟩ := Filter.frequently_atTop.mp hfreq 0
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm]
  have h1 : ‖z k - x‖ ≤ ‖z N - x‖ := hanti x hxC N k hk
  have h2 : ‖z N - x‖ < ε := by
    rw [Metric.mem_ball, dist_eq_norm] at hNb
    exact hNb
  linarith
