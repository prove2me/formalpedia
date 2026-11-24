-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLevyAnnulusRestrictEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:10:37.239802+00:00
-- url     : https://prove2.me/submissions/491d7dca-c598-44c3-b425-40e36ce44348

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hs : ν (Set.Iio (0 : ℝ)) = 0) (r : ℝ) :
    ν.restrict {x : ℝ | r ≤ |x| ∧ |x| < 1} = ν.restrict (Set.Ico r 1) := by
  have hpos : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]
    simpa only [Set.Iio, not_le] using hs
  apply Measure.restrict_congr_set
  filter_upwards [hpos] with x hx
  change (r ≤ |x| ∧ |x| < 1) = (r ≤ x ∧ x < 1)
  rw [abs_of_nonneg hx]
