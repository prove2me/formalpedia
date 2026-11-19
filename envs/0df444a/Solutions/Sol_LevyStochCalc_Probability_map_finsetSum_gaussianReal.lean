-- Prove2me | solution 1 for LevyStochCalc.Probability.map_finsetSum_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:48:47.44417+00:00
-- url     : https://prove2.me/submissions/fc083ff0-f5ca-47c2-bf52-2cfbe5658627

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A finite sum of independent centred Gaussians

Adding one summand at a time, using that the sum of two independent Gaussians is Gaussian with
the sum of the variances.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]



theorem _root_.solution {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {v : ι → ℝ≥0}
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, gaussianReal_zero_var]
    rw [Measure.map_const]; simp
  | insert i s hi ih =>
    have hfun : (fun ω => ∑ j ∈ insert i s, X j ω) = (∑ j ∈ s, X j) + X i := by
      funext ω; rw [Finset.sum_insert hi, Pi.add_apply, Finset.sum_apply, add_comm]
    have ih' : P.map (∑ j ∈ s, X j) = gaussianReal 0 (∑ j ∈ s, v j) := by
      have : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by funext ω; rw [Finset.sum_apply]
      rw [this, ih]
    rw [hfun, Finset.sum_insert hi,
      gaussianReal_add_gaussianReal_of_indepFun (hind.indepFun_finsetSum_of_notMem hX hi) ih' (hlaw i)]
    simp [add_comm]
