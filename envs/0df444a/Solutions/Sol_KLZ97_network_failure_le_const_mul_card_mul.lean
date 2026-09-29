-- Prove2me | solution 1 for KLZ97.network_failure_le_const_mul_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:49:02.365182+00:00
-- url     : https://prove2.me/submissions/47aa6750-8513-41ce-b518-9e7703990938

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

theorem solution {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (locs : Finset ι) (fail : ι → Set Ω) (C p : ENNReal)
    (hmodel : QuasiIndepMonotone μ locs fail C p) :
    μ (⋃ i ∈ locs, fail i) ≤ C * locs.card * p := by
  classical
  calc μ (⋃ i ∈ locs, fail i) ≤ ∑ i ∈ locs, μ (fail i) := MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ locs, C * p := by
        apply Finset.sum_le_sum
        intro i hi
        have := hmodel {i} (by simpa using hi)
        simpa using this
    _ = C * locs.card * p := by simp; ring
