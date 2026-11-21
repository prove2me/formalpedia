-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_positive_open_clock_eq_all_times
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T22:37:49.655416+00:00
-- url     : https://prove2.me/submissions/a39f1e71-3e96-4bb1-a506-d6bf19c5df14

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (S : Set ℝ) (hS : IsOpen S)
    (hright : ∀ t, ContinuousWithinAt f (Ici t) t) :
    sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧ f u ∈ S} =
      ⨅ (u : ℝ≥0) (_ : f u ∈ S), (u : ℝ≥0∞) := by
  apply le_antisymm
  · refine le_iInf₂ fun u hu => ?_
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hpos
    · subst h0
      have hev : ∀ᶠ v : ℝ≥0 in 𝓝[Ioi (0 : ℝ≥0)] (0 : ℝ≥0), f v ∈ S :=
        nhdsWithin_mono _ Ioi_subset_Ici_self
          ((hright 0).tendsto.eventually (hS.mem_nhds hu))
      have hle : ∀ᶠ v : ℝ≥0 in 𝓝[Ioi (0 : ℝ≥0)] (0 : ℝ≥0),
          sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = t ∧ f u ∈ S} ≤ (v : ℝ≥0∞) := by
        filter_upwards [hev, self_mem_nhdsWithin] with v hv hvpos
        exact sInf_le ⟨v, hvpos, rfl, hv⟩
      have htend : Tendsto (fun v : ℝ≥0 => (v : ℝ≥0∞)) (𝓝[Ioi (0 : ℝ≥0)] (0 : ℝ≥0))
          (𝓝 ((0 : ℝ≥0) : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto htend hle
    · exact sInf_le ⟨u, hpos, rfl, hu⟩
  · refine le_sInf ?_
    rintro t ⟨u, -, rfl, hu⟩
    exact iInf₂_le u hu
