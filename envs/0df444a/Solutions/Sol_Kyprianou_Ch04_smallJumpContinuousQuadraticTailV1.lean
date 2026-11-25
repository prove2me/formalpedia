-- Prove2me | solution 1 for Kyprianou.Ch04.smallJumpContinuousQuadraticTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:17:48.705977+00:00
-- url     : https://prove2.me/submissions/e68c4e70-f893-4aaa-9b1c-e7a66ffc0fcb

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_smallJumpReciprocalQuadraticTailV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Arbitrary positive real cutoffs, rather than only sequences. -/
theorem solution (ν : Measure ℝ) (hν : IsLevyMeasure ν) :
    Tendsto (fun r : ℝ => ∫⁻ z in {z : ℝ | |z| ≤ r},
      ENNReal.ofReal (z ^ 2) ∂ν) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have ht := Kyprianou.Ch04.smallJumpReciprocalQuadraticTailV1 ν hν
  apply tendsto_order.2
  constructor
  · intro a ha
    exact (not_lt_of_ge (zero_le : 0 ≤ a) ha).elim
  · intro a ha
    have he := (tendsto_order.1 ht).2 a ha
    obtain ⟨n, hn⟩ := eventually_atTop.1 he
    have hr : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), r < 1 / ((n : ℝ) + 2) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    filter_upwards [hr] with r hr
    exact (lintegral_mono' (Measure.restrict_mono (fun z hz => le_trans hz hr.le) le_rfl) le_rfl).trans_lt (hn n le_rfl)
