-- Prove2me | solution 1 for MarkovProcess.tendsto_dyadicTime_dyadicIndex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:30:59.4018+00:00
-- url     : https://prove2.me/submissions/559eaed5-bf01-4b19-aeb1-e34f79a9eca1

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.EMetricSpace.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic chaining on a bounded interval of nonnegative time

This file is deterministic infrastructure for a quantitative modulus of continuity.  It
subdivides the interval `[0, T]` of nonnegative real time into `2 ^ m` equal parts and records
what uniform control of the adjacent increments of a function `f : ℝ≥0 → E` on all subdivisions
from a base level downwards implies for pairs of subdivision points.

Main results:

* `MarkovProcess.dyadicTime`, the `i`-th point of the level-`m` subdivision of `[0, T]`, with its
  monotonicity, refinement and increment estimates;
* `MarkovProcess.HasDyadicAdjacentBound`, the hypothesis that all adjacent increments of `f` on
  the level-`m` subdivision are at most `e`;
* `MarkovProcess.edist_dyadicTime_le_of_hasDyadicAdjacentBound`, the same-level chaining bound;
* `MarkovProcess.edist_dyadicTime_ancestor_le`, the bound from a fine subdivision point to its
  canonical coarse ancestor by the sum of the intervening bounds;
* `MarkovProcess.edist_dyadicTime_le_of_sub_le`, the two-point chaining bound: subdivision points
  of level `n + r` whose indices differ by at most `2 ^ r` are within `2 * (chain sum) + e n`;
* `MarkovProcess.dyadicIndex` and its approximation lemmas, which locate an arbitrary time of
  `[0, T]` between consecutive subdivision points and compare the indices of two nearby times.

Everything here is a statement about a fixed function of time.  No measure, no probability law,
and no continuity of `f` is used or asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess

section Subdivision



theorem dyadicTime_coe (T : ℝ≥0) (m i : ℕ) :
    ((dyadicTime T m i : ℝ≥0) : ℝ) = (T : ℝ) * i / 2 ^ m := by
  simp [dyadicTime]













end Subdivision

section Chaining

variable {E : Type*} [PseudoEMetricSpace E]











end Chaining

section Approximation







theorem dyadicTime_dyadicIndex_le {T : ℝ≥0} (hT : 0 < T) (m : ℕ) (s : ℝ≥0) :
    dyadicTime T m (dyadicIndex T m s) ≤ s := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hx0 : (0 : ℝ) ≤ (s : ℝ) * 2 ^ m / T := by positivity
  have hfloor : ((dyadicIndex T m s : ℕ) : ℝ) ≤ (s : ℝ) * 2 ^ m / T := Nat.floor_le hx0
  rw [← NNReal.coe_le_coe, dyadicTime_coe, div_le_iff₀ hpow]
  calc (T : ℝ) * ((dyadicIndex T m s : ℕ) : ℝ) ≤ (T : ℝ) * ((s : ℝ) * 2 ^ m / T) :=
        mul_le_mul_of_nonneg_left hfloor T.coe_nonneg
    _ = (s : ℝ) * 2 ^ m := by field_simp

theorem le_dyadicTime_dyadicIndex_add {T : ℝ≥0} (hT : 0 < T) (m : ℕ) (s : ℝ≥0) :
    s ≤ dyadicTime T m (dyadicIndex T m s) + T / 2 ^ m := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hfloor : (s : ℝ) * 2 ^ m / T < ((dyadicIndex T m s : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hlt : (s : ℝ) * 2 ^ m < (((dyadicIndex T m s : ℕ) : ℝ) + 1) * T :=
    (div_lt_iff₀ hT').mp hfloor
  rw [← NNReal.coe_le_coe]
  push_cast [dyadicTime_coe]
  rw [← add_div, le_div_iff₀ hpow]
  nlinarith [hlt]





end Approximation

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic chaining on a bounded interval of nonnegative time

This file is deterministic infrastructure for a quantitative modulus of continuity.  It
subdivides the interval `[0, T]` of nonnegative real time into `2 ^ m` equal parts and records
what uniform control of the adjacent increments of a function `f : ℝ≥0 → E` on all subdivisions
from a base level downwards implies for pairs of subdivision points.

Main results:

* `MarkovProcess.dyadicTime`, the `i`-th point of the level-`m` subdivision of `[0, T]`, with its
  monotonicity, refinement and increment estimates;
* `MarkovProcess.HasDyadicAdjacentBound`, the hypothesis that all adjacent increments of `f` on
  the level-`m` subdivision are at most `e`;
* `MarkovProcess.edist_dyadicTime_le_of_hasDyadicAdjacentBound`, the same-level chaining bound;
* `MarkovProcess.edist_dyadicTime_ancestor_le`, the bound from a fine subdivision point to its
  canonical coarse ancestor by the sum of the intervening bounds;
* `MarkovProcess.edist_dyadicTime_le_of_sub_le`, the two-point chaining bound: subdivision points
  of level `n + r` whose indices differ by at most `2 ^ r` are within `2 * (chain sum) + e n`;
* `MarkovProcess.dyadicIndex` and its approximation lemmas, which locate an arbitrary time of
  `[0, T]` between consecutive subdivision points and compare the indices of two nearby times.

Everything here is a statement about a fixed function of time.  No measure, no probability law,
and no continuity of `f` is used or asserted.
-/

open Filter Topology
open scoped ENNReal NNReal















namespace MarkovProcess
end MarkovProcess
open MarkovProcess
theorem solution {T : ℝ≥0} (hT : 0 < T) (s : ℝ≥0) :
    Tendsto (fun m ↦ dyadicTime T m (dyadicIndex T m s)) atTop (𝓝 s) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hzero : Tendsto (fun m : ℕ ↦ (T : ℝ) / 2 ^ m) atTop (𝓝 0) := by
    have hhalf : Tendsto (fun m : ℕ ↦ ((1 : ℝ) / 2) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul := hhalf.const_mul (T : ℝ)
    rw [mul_zero] at hmul
    refine hmul.congr fun m ↦ ?_
    rw [div_pow, one_pow]
    ring
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun m ↦ ?_) hzero
  have h1 : ((dyadicTime T m (dyadicIndex T m s) : ℝ≥0) : ℝ) ≤ (s : ℝ) :=
    dyadicTime_dyadicIndex_le hT m s
  have h2 : (s : ℝ) ≤ ((dyadicTime T m (dyadicIndex T m s) : ℝ≥0) : ℝ) + (T : ℝ) / 2 ^ m := by
    have h := NNReal.coe_le_coe.mpr (le_dyadicTime_dyadicIndex_add hT m s)
    push_cast at h
    exact h
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith
