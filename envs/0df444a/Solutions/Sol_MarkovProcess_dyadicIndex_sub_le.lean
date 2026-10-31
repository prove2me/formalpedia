-- Prove2me | solution 1 for MarkovProcess.dyadicIndex_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:27:38.815186+00:00
-- url     : https://prove2.me/submissions/bec3f369-aafe-4fd8-b972-b65046fb0282

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

















end Subdivision

section Chaining

variable {E : Type*} [PseudoEMetricSpace E]











end Chaining

section Approximation















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
theorem solution {T : ℝ≥0} (hT : 0 < T) {s t : ℝ≥0} {n r : ℕ}
    (hr : 1 ≤ r) (hd : t ≤ s + T / 2 ^ (n + 1)) :
    dyadicIndex T (n + r) t - dyadicIndex T (n + r) s ≤ 2 ^ r := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ (n + r) := by positivity
  set i : ℕ := dyadicIndex T (n + r) s with hi
  set j : ℕ := dyadicIndex T (n + r) t with hj
  have hjle : (j : ℝ) ≤ (t : ℝ) * 2 ^ (n + r) / T := Nat.floor_le (by positivity)
  have hilt : (s : ℝ) * 2 ^ (n + r) / T < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdreal : (t : ℝ) ≤ (s : ℝ) + (T : ℝ) / 2 ^ (n + 1) := by
    have := NNReal.coe_le_coe.mpr hd
    push_cast at this
    exact this
  have hsplit : (2 : ℝ) ^ (n + r) = 2 ^ (n + 1) * 2 ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hstep : (t : ℝ) * 2 ^ (n + r) ≤
      (s : ℝ) * 2 ^ (n + r) + (2 : ℝ) ^ (r - 1) * T := by
    have hmul : (t : ℝ) * 2 ^ (n + r) ≤
        ((s : ℝ) + (T : ℝ) / 2 ^ (n + 1)) * 2 ^ (n + r) := by
      gcongr
    refine hmul.trans (le_of_eq ?_)
    rw [hsplit]
    field_simp
  have h1 : (j : ℝ) * T ≤ (t : ℝ) * 2 ^ (n + r) := by
    rwa [le_div_iff₀ hT'] at hjle
  have h2 : (s : ℝ) * 2 ^ (n + r) < ((i : ℝ) + 1) * T := (div_lt_iff₀ hT').mp hilt
  have h3 : (j : ℝ) * T < ((i : ℝ) + 1 + (2 : ℝ) ^ (r - 1)) * T := by
    have hexpand : ((i : ℝ) + 1 + (2 : ℝ) ^ (r - 1)) * T
        = ((i : ℝ) + 1) * T + (2 : ℝ) ^ (r - 1) * T := by ring
    rw [hexpand]
    linarith
  have hkey : (j : ℝ) < (i : ℝ) + 1 + (2 : ℝ) ^ (r - 1) :=
    lt_of_mul_lt_mul_right h3 hT'.le
  have hnat : j ≤ i + 2 ^ (r - 1) := by
    have hcast : (j : ℝ) < ((i + 2 ^ (r - 1) + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hcast)
  have hmono : 2 ^ (r - 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfinal : j - i ≤ 2 ^ (r - 1) := tsub_le_iff_right.mpr (by rw [add_comm]; exact hnat)
  exact hfinal.trans hmono
