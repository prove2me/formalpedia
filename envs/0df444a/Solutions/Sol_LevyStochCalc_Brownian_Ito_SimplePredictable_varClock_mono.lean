-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:06:49.35938+00:00
-- url     : https://prove2.me/submissions/bda7fc4c-fbc7-4235-be17-6c95a8e20e83

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)


theorem _root_.solution (c : Fin G.N → ℝ) {k l : ℕ} (h : k ≤ l) :
    G.varClock c k ≤ G.varClock c l := by
  unfold varClock
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun j _ _ => ?_
  split
  · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · exact le_rfl
