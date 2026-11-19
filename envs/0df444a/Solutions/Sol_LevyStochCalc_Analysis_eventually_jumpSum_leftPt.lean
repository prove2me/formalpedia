-- Prove2me | solution 1 for LevyStochCalc.Analysis.eventually_jumpSum_leftPt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:21:50.718119+00:00
-- url     : https://prove2.me/submissions/9ef23214-50b7-4bd3-a75b-81276114a24c

import Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums of finitely many jumps along a dyadic grid

A finite set of points of `ℝ × E` with weights defines a step function of the time,
`jumpSum S c s`, the sum of the weights of the points with time in `(0, s]`, and its strict-past
version `jumpSumStrict S c s`. Along the dyadic grid of `[0, t]` the frozen values
`jumpSum S c (leftPt t n s)` are eventually the strict-past value, and the sums of the increments
over the cells weighted by a continuous function at the right endpoints converge to the sum of
the weights times the function at the points. A finite sum of Dirac masses integrates a function
over a time window to such a jump sum.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace LevyStochCalc.Analysis

variable {E : Type*}

section Sums



theorem _root_.solution (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, jumpSum S c (leftPt t n s) = jumpSumStrict S c s := by
  have h0 : Tendsto (fun n : ℕ => t / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hall : ∀ᶠ n : ℕ in atTop, ∀ p ∈ S, (p.1 ≤ leftPt t n s ↔ p.1 < s) := by
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases hp : p.1 < s
    · have hpos : 0 < s - p.1 := by linarith
      filter_upwards [h0.eventually (gt_mem_nhds hpos)] with n hn
      have h1 := le_leftPt_add ht n hs
      constructor
      · intro _; exact hp
      · intro _; linarith
    · refine Filter.Eventually.of_forall fun n => ?_
      have h1 := leftPt_lt ht n hs
      constructor
      · intro h; exact absurd (lt_of_le_of_lt h h1) hp
      · intro h; exact absurd h hp
  filter_upwards [hall] with n hn
  rw [jumpSum, jumpSumStrict]
  refine Finset.sum_congr rfl fun p hp => ?_
  have := hn p hp
  by_cases h1 : 0 < p.1 ∧ p.1 < s
  · rw [if_pos ⟨h1.1, this.2 h1.2⟩, if_pos h1]
  · rw [if_neg (fun h => h1 ⟨h.1, this.1 h.2⟩), if_neg h1]

