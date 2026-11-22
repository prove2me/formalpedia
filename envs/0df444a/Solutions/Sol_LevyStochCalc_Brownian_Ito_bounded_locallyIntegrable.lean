-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.bounded_locallyIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:39:02.969049+00:00
-- url     : https://prove2.me/submissions/7b0136e7-907a-4fa4-86c1-96d9e59bb2c2

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable.



theorem _root_.solution
    (g : ℝ → ℝ) (h_meas : Measurable g) (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) :
    MeasureTheory.LocallyIntegrable g volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  haveI : IsFiniteMeasure (volume.restrict K : Measure ℝ) :=
    ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure ℝ))⟩
  refine (integrable_const M).mono' h_meas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s => by
    simpa only [Real.norm_eq_abs] using h_bound s
