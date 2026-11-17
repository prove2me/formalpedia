-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:17:45.739568+00:00
-- url     : https://prove2.me/submissions/cc80ff4e-032a-4653-a5e6-279bd71db964

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem finite_large_jumps_of_nnreal_cadlag
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l) ∧
        δ < |Y u - l|}.Finite := by
  set A := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l) ∧ δ < |Y u - l|} with hA
  -- a point of A cannot lie in a window where Y stays within δ/3 of a constant c
  have key : ∀ (u : ℝ≥0) (c : ℝ) (W : Set ℝ≥0), u ∈ A → W ∈ 𝓝[<] u →
      (∀ v ∈ W, |Y v - c| < δ / 3) → |Y u - c| < δ / 3 → False := by
    intro u c W hu hW hWc huc
    obtain ⟨hu0, -, l, hl, hjump⟩ := hu
    haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
    have hb : ∀ᶠ v in 𝓝[<] u, |Y v - c| ≤ δ / 3 :=
      Filter.mem_of_superset hW fun v hv => (hWc v hv).le
    have hlc : |l - c| ≤ δ / 3 := le_of_tendsto ((hl.sub_const c).abs) hb
    have : |Y u - l| ≤ |Y u - c| + |l - c| := by
      calc |Y u - l| = |(Y u - c) - (l - c)| := by ring_nf
        _ ≤ |Y u - c| + |l - c| := abs_sub _ _
    linarith
  by_contra hinf
  obtain ⟨s, -, hs⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ≥0) T)) (fun u hu => ⟨bot_le, hu.2.1⟩)
  rw [accPt_iff_frequently_nhdsNE] at hs
  apply hs
  rw [← nhdsLT_sup_nhdsGT, eventually_sup]
  constructor
  · -- left of s
    rcases eq_or_lt_of_le (bot_le : (0:ℝ≥0) ≤ s) with h0 | hs0
    · subst h0
      rw [Set.Iio_bot, nhdsWithin_empty]
      exact Filter.eventually_bot
    · obtain ⟨L, hLs⟩ := hL s hs0
      have hG : ∀ᶠ v in 𝓝[<] s, |Y v - L| < δ / 3 := by
        have := hLs.eventually (Metric.ball_mem_nhds L (by positivity : (0:ℝ) < δ / 3))
        filter_upwards [this] with v hv
        simpa [Real.dist_eq] using hv
      obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs0).1 hG
      filter_upwards [Ioo_mem_nhdsLT ha] with u hu huA
      exact key u L (Ioo a u) huA (Ioo_mem_nhdsLT hu.1)
        (fun v hv => hsub ⟨hv.1, hv.2.trans hu.2⟩) (hsub hu)
  · -- right of s
    have hG : ∀ᶠ v in 𝓝[≥] s, |Y v - Y s| < δ / 3 := by
      have := (hR s).eventually (Metric.ball_mem_nhds (Y s) (by positivity : (0:ℝ) < δ / 3))
      filter_upwards [this] with v hv
      simpa [Real.dist_eq] using hv
    obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hG
    filter_upwards [Ioo_mem_nhdsGT hb] with u hu huA
    exact key u (Y s) (Ioo s u) huA (Ioo_mem_nhdsLT hu.1)
      (fun v hv => hsub ⟨hv.1.le, hv.2.trans hu.2⟩) (hsub ⟨hu.1.le, hu.2⟩)

end Kyprianou.ProofPreparation

theorem solution
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l))
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l) ∧
        δ < |Y u - l|}.Finite := by
  first
  | exact Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag
  | exact Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag ..
  | (apply Kyprianou.ProofPreparation.finite_large_jumps_of_nnreal_cadlag <;> assumption)
