-- Prove2me | solution 1 for Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:03:58.894427+00:00
-- url     : https://prove2.me/submissions/e084ddb0-7074-4aa7-ab62-949d0bc80170

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem exists_tendsto_of_uniform_approx
    {α : Type} (L : Filter α) [L.NeBot]
    (s : Set α) (hs : s ∈ L)
    (fn : ℕ → α → ℝ) (f : α → ℝ)
    (hfn : ∀ n, ∃ a : ℝ, Tendsto (fn n) L (𝓝 a))
    (huni : ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ y ∈ s, |fn n y - f y| < ε) :
    ∃ a : ℝ, Tendsto f L (𝓝 a) := by
  choose a ha using hfn
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := huni (ε / 3) (by positivity)
    refine ⟨n₀, fun n hn => ?_⟩
    have hlim : Tendsto (fun y => fn n y - fn n₀ y) L (𝓝 (a n - a n₀)) := (ha n).sub (ha n₀)
    have hb : ∀ᶠ y in L, |fn n y - fn n₀ y| ≤ 2 * (ε / 3) := by
      filter_upwards [hs] with y hy
      have h1 := hn₀ n hn y hy
      have h2 := hn₀ n₀ le_rfl y hy
      calc |fn n y - fn n₀ y| = |(fn n y - f y) - (fn n₀ y - f y)| := by ring_nf
        _ ≤ |fn n y - f y| + |fn n₀ y - f y| := abs_sub _ _
        _ ≤ 2 * (ε / 3) := by linarith
    have := le_of_tendsto (hlim.abs) hb
    rw [Real.dist_eq]
    linarith
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨ℓ, TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto (p := atTop) (F := fn) ?_
    (Eventually.of_forall ha) hℓ⟩
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨n₀, hn₀⟩ := huni ε hε
  have : ∀ᶠ p : ℕ × α in atTop ×ˢ L, p.1 ≥ n₀ ∧ p.2 ∈ s :=
    (eventually_ge_atTop n₀).prod_mk hs
  filter_upwards [this] with p hp
  apply hεu
  rw [Real.dist_eq, abs_sub_comm]
  exact hn₀ p.1 hp.1 p.2 hp.2

end Kyprianou.ProofPreparation

theorem solution
    {α : Type} (L : Filter α) [L.NeBot]
    (s : Set α) (hs : s ∈ L)
    (fn : ℕ → α → ℝ) (f : α → ℝ)
    (hfn : ∀ n, ∃ a : ℝ, Tendsto (fn n) L (𝓝 a))
    (huni : ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ y ∈ s, |fn n y - f y| < ε) :
    ∃ a : ℝ, Tendsto f L (𝓝 a) := by
  first
  | exact Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx
  | exact Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx ..
  | (apply Kyprianou.ProofPreparation.exists_tendsto_of_uniform_approx <;> assumption)
