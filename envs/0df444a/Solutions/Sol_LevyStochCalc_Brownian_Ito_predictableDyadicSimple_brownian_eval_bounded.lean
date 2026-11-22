-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_bounded
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:41:57.920666+00:00
-- url     : https://prove2.me/submissions/a56972d6-7a6f-4b07-b158-c6a216afb3c7

import Theorems.Thm_LevyStochCalc_Brownian_Ito_partition_intervals_disjoint
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F000

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
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) :
    |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω|
      ≤ max M 0 := by
  classical
  let H := predictableDyadicSimple_brownian hT g h_meas M h_bound n
  change |H.eval s ω| ≤ max M 0
  let J (i : Fin H.N) := Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
  rw [eval_eq_sum_indicator]
  change |∑ i : Fin H.N, (J i).indicator (fun _ => H.ξ i ω) s| ≤ max M 0
  by_cases h : ∃ i : Fin H.N, s ∈ J i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hi]
      exact dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i ω
    · intro j _ hj
      have hd := (partition_intervals_disjoint H) hj
      exact Set.indicator_of_notMem (fun hm => Set.disjoint_left.mp hd hm hi) _
    · simp
  · have hh (i : Fin H.N) : s ∉ J i := fun hi => h ⟨i, hi⟩
    simp [Set.indicator_of_notMem, hh, le_max_right]
