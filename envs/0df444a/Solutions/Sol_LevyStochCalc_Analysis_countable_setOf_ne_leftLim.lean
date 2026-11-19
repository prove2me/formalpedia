-- Prove2me | solution 1 for LevyStochCalc.Analysis.countable_setOf_ne_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:14:38.112779+00:00
-- url     : https://prove2.me/submissions/53615dd6-391a-42f0-8e05-4de4608cb04c

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jumps of a càdlàg function

A function on the line that is right-continuous and has left limits everywhere jumps only at
isolated points of each level of the jump size, so its jump set is countable and therefore
Lebesgue-null: such a function agrees with its left limits almost everywhere.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace LevyStochCalc.Analysis



theorem _root_.solution {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    {t : ℝ | f t ≠ Function.leftLim f t}.Countable := by
  -- local smallness of jumps to the right of any point
  have key : ∀ x : ℝ, ∀ ε > 0, ∃ y, x < y ∧ ∀ u ∈ Set.Ioo x y,
      |f u - Function.leftLim f u| < ε := by
    intro x ε hε
    have hε3 : 0 < ε / 3 := by positivity
    have hev := (hright x).eventually (Metric.ball_mem_nhds (f x) hε3)
    obtain ⟨y, hxy, hy⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
    refine ⟨y, hxy, fun u hu => ?_⟩
    obtain ⟨L, hL⟩ := hleft u
    have hLeq : Function.leftLim f u = L := leftLim_eq_of_tendsto hL
    have hLball : L ∈ Metric.closedBall (f x) (ε / 3) := by
      refine Metric.isClosed_closedBall.mem_of_tendsto hL ?_
      filter_upwards [Ioo_mem_nhdsLT hu.1] with v hv
      exact Metric.ball_subset_closedBall (hy ⟨hv.1, hv.2.trans hu.2⟩)
    have hfu : f u ∈ Metric.ball (f x) (ε / 3) := hy hu
    rw [Metric.mem_ball, Real.dist_eq] at hfu
    rw [Metric.mem_closedBall, Real.dist_eq] at hLball
    rw [hLeq]
    calc |f u - L| = |(f u - f x) - (L - f x)| := by ring_nf
      _ ≤ |f u - f x| + |L - f x| := abs_sub _ _
      _ < ε := by linarith
  let A : ℕ → Set ℝ := fun n => {t | 1 / ((n : ℝ) + 1) < |f t - Function.leftLim f t|}
  have hA : ∀ n, (A n).Countable := by
    intro n
    refine Set.Countable.mono ?_ (countable_setOfPred_isolated_right_within (s := A n))
    intro x hx
    refine ⟨hx, ?_⟩
    obtain ⟨y, hxy, hy⟩ := key x (1 / ((n : ℝ) + 1)) (by positivity)
    rw [← Filter.empty_mem_iff_bot, mem_nhdsWithin]
    refine ⟨Set.Iio y, isOpen_Iio, hxy, ?_⟩
    rintro u ⟨huy, huA, hux⟩
    exact absurd huA (not_lt.2 (hy u ⟨hux, huy⟩).le)
  refine (Set.countable_iUnion hA).mono (fun t ht => ?_)
  have hpos : 0 < |f t - Function.leftLim f t| := abs_pos.2 (sub_ne_zero.2 ht)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact Set.mem_iUnion.2 ⟨n, hn⟩

