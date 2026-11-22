-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.eval_sq_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:36:13.668488+00:00
-- url     : https://prove2.me/submissions/f1056855-657f-4233-afe1-dd06b9df5bf3

import Theorems.Thm_LevyStochCalc_Brownian_Ito_partition_intervals_disjoint
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple predictable integrands and the elementary Brownian integral

The class `SimplePredictable` of integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` with bounded
measurable coefficients, their pointwise evaluation `SimplePredictable.eval`, the elementary
integral `simpleIntegral` against a scalar Brownian motion `W`, and the energy
`∫⁻ ‖H.eval s ω‖₊ ^ 2` of the integrand, which the disjointness of the partition intervals
`(t_i, t_{i+1}]` turns into the sum `∑_i (t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊ ^ 2 ∂P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution
    {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s := by
  classical
  let J (i : Fin H.N) := Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
  have hd : Pairwise (fun i j => Disjoint (J i) (J j)) := partition_intervals_disjoint H
  have he : H.eval s ω = ∑ i : Fin H.N, (J i).indicator (fun _ => H.ξ i ω) s := by
    first | exact H.eval_eq_sum_indicator s ω | exact eval_eq_sum_indicator H s ω | rfl
  rw [he]
  change (‖∑ i : Fin H.N, (J i).indicator (fun _ => H.ξ i ω) s‖₊ : ℝ≥0∞) ^ 2 =
    ∑ i : Fin H.N, (J i).indicator (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s
  by_cases hex : ∃ i : Fin H.N, s ∈ J i
  · obtain ⟨i, hi⟩ := hex
    have hn (j : Fin H.N) (hji : j ≠ i) : s ∉ J j :=
      fun hj => (Set.disjoint_left.mp (hd hji)) hj hi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hi]
    · intro j _ hj
      exact Set.indicator_of_notMem (hn j hj) _
    · simp
    · intro j _ hj
      exact Set.indicator_of_notMem (hn j hj) _
    · simp
  · have hn (i : Fin H.N) : s ∉ J i := fun hi => hex ⟨i, hi⟩
    simp [Set.indicator_of_notMem, hn]
