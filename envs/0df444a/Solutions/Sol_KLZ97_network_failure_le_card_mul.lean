-- Prove2me | solution 1 for KLZ97.network_failure_le_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:48:50.066917+00:00
-- url     : https://prove2.me/submissions/3766cd9c-35a8-49d3-b0dd-e66dd9bda256

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

theorem solution {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (locs : Finset ι) (fail : ι → Set Ω) (p : ENNReal)
    (hmodel : QuasiIndepStochastic μ locs fail p) :
    μ (⋃ i ∈ locs, fail i) ≤ locs.card * p := by
  classical
  calc μ (⋃ i ∈ locs, fail i) ≤ ∑ i ∈ locs, μ (fail i) := MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ locs, p := by
        apply Finset.sum_le_sum
        intro i hi
        have := hmodel {i} (by simpa using hi)
        simpa using this
    _ = locs.card * p := by simp
