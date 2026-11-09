-- Prove2me | solution 1 for NoRegretLastIterate.claim_3_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:50:26.166092+00:00
-- url     : https://prove2.me/submissions/8e330a9a-a341-4fef-84a2-d00e48462b91

import Mathlib

open MeasureTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : ℕ → Ω → ℝ) {q : ℝ}
    (hq : 0 < q ∧ q < 1) (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω) atTop (𝓝 q)) :
    ∀ᵐ ω ∂μ, ∀ t : ℕ → ℕ, StrictMono t →
      Tendsto (fun k => ((({s ∈ Finset.range (t k) | q / 2 ≤ Q s ω ∧ Q s ω ≤ (q + 1) / 2} :
        Finset ℕ).card : ℝ) / (t k : ℝ))) atTop (𝓝 1) := by
  obtain ⟨hq0, hq1⟩ := hq
  filter_upwards [hconv] with ω hω
  intro t ht
  have hev : ∀ᶠ s in atTop, Q s ω ∈ Set.Icc (q / 2) ((q + 1) / 2) :=
    hω (Icc_mem_nhds (by linarith) (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have htN : Tendsto t atTop atTop := ht.tendsto_atTop
  have htk : Tendsto (fun k => (t k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htN
  set c : ℕ → ℕ := fun k => ({s ∈ Finset.range (t k) | q / 2 ≤ Q s ω ∧ Q s ω ≤ (q + 1) / 2} :
    Finset ℕ).card with hc
  have hlow : ∀ k, t k ≤ c k + N := by
    intro k
    have hsub : Finset.Ico N (t k) ⊆
        ({s ∈ Finset.range (t k) | q / 2 ≤ Q s ω ∧ Q s ω ≤ (q + 1) / 2} : Finset ℕ) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hs.2, hN s hs.1⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    show t k ≤ c k + N
    simp only [hc]
    omega
  have hup : ∀ k, c k ≤ t k := by
    intro k
    have := Finset.card_filter_le (Finset.range (t k))
      (fun s => q / 2 ≤ Q s ω ∧ Q s ω ≤ (q + 1) / 2)
    rw [Finset.card_range] at this
    exact this
  have hlim : Tendsto (fun k => 1 - (N : ℝ) / (t k : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (N : ℝ))).div_atTop htk
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hpos : ∀ᶠ k in atTop, 1 ≤ t k := htN.eventually_ge_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [hpos] with k hk
    have htpos : (0:ℝ) < t k := by exact_mod_cast hk
    have h1 : ((t k : ℕ) : ℝ) ≤ (c k : ℝ) + N := by exact_mod_cast hlow k
    show 1 - (N : ℝ) / (t k : ℝ) ≤ (c k : ℝ) / (t k : ℝ)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ htpos]
    linarith
  · filter_upwards [hpos] with k hk
    have htpos : (0:ℝ) < t k := by exact_mod_cast hk
    show (c k : ℝ) / (t k : ℝ) ≤ 1
    rw [div_le_one htpos]
    exact_mod_cast hup k
