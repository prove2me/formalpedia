-- Prove2me | solution 1 for IncProx.Cyclic.footnote5_deterministic_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:42:48.686414+00:00
-- url     : https://prove2.me/submissions/38d5b067-d6d5-499f-a526-1386edd376f6

import Mathlib
set_option autoImplicit false
open Filter Topology

theorem solution (Y Z W : ℕ → ℝ) (hY : ∀ k, 0 ≤ Y k)
    (hZ : ∀ k, 0 ≤ Z k) (hW : ∀ k, 0 ≤ W k) (hrec : ∀ k, Y (k + 1) ≤ Y k - Z k + W k)
    (hsum : Summable W) : ∃ L : ℝ, Tendsto Y atTop (𝓝 L) := by
  set T : ℕ → ℝ := fun k => ∑' i, W (i + k) with hTdef
  have hs : ∀ k, (∑ i ∈ Finset.range k, W i) + T k = ∑' i, W i := fun k => hsum.sum_add_tsum_nat_add k
  have hT : ∀ k, T k = W k + T (k + 1) := by
    intro k
    have h1 := hs k
    have h2 := hs (k + 1)
    rw [Finset.sum_range_succ] at h2
    linarith
  have hT0 : ∀ k, 0 ≤ T k := fun k => tsum_nonneg (fun i => hW _)
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add W
  set V : ℕ → ℝ := fun k => Y k + T k with hVdef
  have hVanti : Antitone V := by
    apply antitone_nat_of_succ_le
    intro k
    have := hrec k
    have := hT k
    have := hZ k
    simp only [hVdef]
    linarith
  have hVbdd : BddBelow (Set.range V) := ⟨0, by
    rintro _ ⟨k, rfl⟩
    exact add_nonneg (hY k) (hT0 k)⟩
  have hVlim := tendsto_atTop_ciInf hVanti hVbdd
  refine ⟨(⨅ i, V i) - 0, ?_⟩
  have := hVlim.sub hTlim
  refine this.congr (fun k => ?_)
  simp [hVdef]
