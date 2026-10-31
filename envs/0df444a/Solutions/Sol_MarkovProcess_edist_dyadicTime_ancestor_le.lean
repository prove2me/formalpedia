-- Prove2me | solution 1 for MarkovProcess.edist_dyadicTime_ancestor_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:02.425858+00:00
-- url     : https://prove2.me/submissions/16325df8-2e19-4ebb-99dd-1b10e6a1be0b

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







/-- A subdivision point of level `m` is a subdivision point of level `m + 1`. -/
theorem dyadicTime_succ_level (T : ℝ≥0) (m i : ℕ) :
    dyadicTime T (m + 1) (2 * i) = dyadicTime T m i := by
  rw [← NNReal.coe_inj, dyadicTime_coe, dyadicTime_coe]
  push_cast
  rw [pow_succ]
  field_simp





end Subdivision

section Chaining

variable {E : Type*} [PseudoEMetricSpace E]





/-- Child-to-parent chaining: a level-`m + 1` subdivision point is within one adjacent bound of
the level-`m` point obtained by halving its index. -/
theorem edist_dyadicTime_parent_le {f : ℝ≥0 → E} {T : ℝ≥0} {m : ℕ} {e : ℝ≥0∞}
    (hf : HasDyadicAdjacentBound f T (m + 1) e) {i : ℕ} (hi : i ≤ 2 ^ (m + 1)) :
    edist (f (dyadicTime T (m + 1) i)) (f (dyadicTime T m (i / 2))) ≤ e := by
  rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
  · have hval : 2 * (i / 2) = i := by omega
    rw [← dyadicTime_succ_level T m (i / 2), hval, edist_self]
    exact zero_le
  · have hval : 2 * (i / 2) + 1 = i := by omega
    have hlt : 2 * (i / 2) < 2 ^ (m + 1) := by omega
    have hbound := hf (2 * (i / 2)) hlt
    rw [hval] at hbound
    rw [← dyadicTime_succ_level T m (i / 2), edist_comm]
    exact hbound





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




variable {E : Type*} [PseudoEMetricSpace E]







namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution {f : ℝ≥0 → E} {T : ℝ≥0} {e : ℕ → ℝ≥0∞} {n : ℕ} :
    ∀ r : ℕ, (∀ k, n < k → k ≤ n + r → HasDyadicAdjacentBound f T k (e k)) →
      ∀ i ≤ 2 ^ (n + r),
        edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T n (i / 2 ^ r))) ≤
          ∑ s ∈ Finset.range r, e (n + s + 1) := by
  intro r
  induction r with
  | zero => intro _ i _; simp
  | succ r ihr =>
      intro hadj i hi
      have hlevel : n + (r + 1) = n + r + 1 := by omega
      have hi' : i ≤ 2 ^ (n + r + 1) := by rwa [← hlevel]
      have hparent : edist (f (dyadicTime T (n + r + 1) i))
          (f (dyadicTime T (n + r) (i / 2))) ≤ e (n + r + 1) :=
        edist_dyadicTime_parent_le (hadj (n + r + 1) (by omega) (by omega)) hi'
      have hpow : 2 ^ (n + r + 1) = 2 ^ (n + r) * 2 := by ring
      have hhalf : i / 2 ≤ 2 ^ (n + r) := by omega
      have hrest := ihr (fun k hk hk' ↦ hadj k hk (by omega)) (i / 2) hhalf
      have hdiv : i / 2 / 2 ^ r = i / 2 ^ (r + 1) := by
        rw [Nat.div_div_eq_div_mul]
        congr 1
        ring
      rw [hdiv] at hrest
      have htri : edist (f (dyadicTime T (n + (r + 1)) i))
            (f (dyadicTime T n (i / 2 ^ (r + 1)))) ≤
          edist (f (dyadicTime T (n + r + 1) i)) (f (dyadicTime T (n + r) (i / 2))) +
            edist (f (dyadicTime T (n + r) (i / 2))) (f (dyadicTime T n (i / 2 ^ (r + 1)))) := by
        rw [hlevel]
        exact edist_triangle _ _ _
      refine htri.trans ((add_le_add hparent hrest).trans_eq ?_)
      rw [Finset.sum_range_succ]
      exact add_comm _ _
