-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulUniformJumpCapTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:24:00.580794+00:00
-- url     : https://prove2.me/submissions/92ec57dd-669b-42d8-b89e-ce5bb5391f5d

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (F : ℕ → ℝ≥0 → ℝ) (f : ℝ≥0 → ℝ)
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (c : ℝ) (hc : c < 1)
    (hcap : ∀ n, ∃ l : ℝ,
      Tendsto (F n) (nhdsWithin t (Set.Iio t)) (nhds l) ∧ |F n t - l| ≤ c)
    (huni : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ s : ℝ≥0, s ≤ T → |F n s - f s| < δ)
    (l : ℝ) (hl : Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    |f t - l| < 1 := by
  let δ : ℝ := (1 - c) / 5
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨n, hn⟩ := huni δ hδ
  obtain ⟨a, ha, hca⟩ := hcap n
  haveI : (nhdsWithin t (Set.Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hstay : ∀ᶠ s in nhdsWithin t (Set.Iio t), s ≤ T := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs.le.trans htT
  have hA : ∀ᶠ s in nhdsWithin t (Set.Iio t), dist (F n s) a < δ :=
    ha.eventually (Metric.ball_mem_nhds _ hδ)
  have hL : ∀ᶠ s in nhdsWithin t (Set.Iio t), dist (f s) l < δ :=
    hl.eventually (Metric.ball_mem_nhds _ hδ)
  obtain ⟨s, ⟨⟨hsA, hsL⟩, hsT⟩⟩ := ((hA.and hL).and hstay).exists
  have h1 : dist (f t) (F n t) < δ := by
    rw [dist_comm]
    simpa only [Real.dist_eq] using hn n le_rfl t htT
  have h2 : dist (F n t) a ≤ c := by simpa only [Real.dist_eq] using hca
  have h3 : dist a (F n s) < δ := by rw [dist_comm]; exact hsA
  have h4 : dist (F n s) (f s) < δ := by
    simpa only [Real.dist_eq] using hn n le_rfl s hsT
  rw [← Real.dist_eq]
  dsimp [δ] at *
  linarith [dist_triangle (f t) (F n t) l, dist_triangle (F n t) a l,
    dist_triangle a (F n s) l, dist_triangle (F n s) (f s) l]
