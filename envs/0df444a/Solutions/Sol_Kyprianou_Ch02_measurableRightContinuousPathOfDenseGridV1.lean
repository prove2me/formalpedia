-- Prove2me | solution 1 for Kyprianou.Ch02.measurableRightContinuousPathOfDenseGridV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:36:56.973805+00:00
-- url     : https://prove2.me/submissions/42bfb888-96d3-4a94-962f-5d884e29bfc2

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Extend measurable grid evaluations by right continuity. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (Y : Ω → ℝ≥0 → ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (hgrid : ∀ k : ℕ, Measurable (fun ω => Y ω (grid k)))
    (hRight : ∀ ω t, ContinuousWithinAt (Y ω) (Ici t) t) :
    Measurable Y := by
  apply measurable_pi_iff.mpr
  intro t
  have hsub : Ioi t ⊆ closure (Ioi t ∩ range grid) :=
    hdense.open_subset_closure_inter isOpen_Ioi
  have ht : t ∈ closure (Ioi t ∩ range grid) := by
    apply closure_minimal hsub isClosed_closure
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr (le_refl t)
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp ht
  have hwithin : Tendsto q atTop (𝓝[Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall (fun n => Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp (hq n).1)))⟩
  have hmeas (n : ℕ) : Measurable (fun ω => Y ω (q n)) := by
    obtain ⟨k, hk⟩ := (hq n).2
    rw [← hk]
    exact hgrid k
  apply measurable_of_tendsto_metrizable hmeas
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (show Tendsto (Y ω) (𝓝[Ici t] t) (𝓝 (Y ω t)) from hRight ω t).comp hwithin
