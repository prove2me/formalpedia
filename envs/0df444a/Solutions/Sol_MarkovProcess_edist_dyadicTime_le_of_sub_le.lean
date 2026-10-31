-- Prove2me | solution 1 for MarkovProcess.edist_dyadicTime_le_of_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:39:31.376709+00:00
-- url     : https://prove2.me/submissions/8595cbeb-1239-4197-893f-f51e128920a1

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.EMetricSpace.Basic
import Theorems.Thm_MarkovProcess_edist_dyadicTime_ancestor_le

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



/-- Same-level chaining: the increment between two subdivision points of the same level is at
most the number of intervening cells times the adjacent bound. -/
theorem edist_dyadicTime_le_of_hasDyadicAdjacentBound {f : ℝ≥0 → E} {T : ℝ≥0} {m : ℕ}
    {e : ℝ≥0∞} (hf : HasDyadicAdjacentBound f T m e) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ m) :
    edist (f (dyadicTime T m i)) (f (dyadicTime T m j)) ≤ (j - i : ℕ) * e := by
  have hchain := edist_le_Ico_sum_of_edist_le (f := fun k ↦ f (dyadicTime T m k)) hij
    (d := fun _ ↦ e) (fun {k} _ hkj ↦ hf k (lt_of_lt_of_le hkj hj))
  simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using hchain







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
theorem solution {f : ℝ≥0 → E} {T : ℝ≥0} {e : ℕ → ℝ≥0∞} {n r : ℕ}
    (hadj : ∀ k, n ≤ k → k ≤ n + r → HasDyadicAdjacentBound f T k (e k))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ (n + r)) (hsub : j - i ≤ 2 ^ r) :
    edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T (n + r) j)) ≤
      2 * (∑ s ∈ Finset.range r, e (n + s + 1)) + e n := by
  have hi : i ≤ 2 ^ (n + r) := hij.trans hj
  have hanc := fun (k : ℕ) (hk : n < k) (hk' : k ≤ n + r) ↦ hadj k hk.le hk'
  have hleft := edist_dyadicTime_ancestor_le (f := f) (T := T) (e := e) (n := n) r hanc i hi
  have hright := edist_dyadicTime_ancestor_le (f := f) (T := T) (e := e) (n := n) r hanc j hj
  have hdivmono : i / 2 ^ r ≤ j / 2 ^ r := Nat.div_le_div_right hij
  have hdivclose : j / 2 ^ r ≤ i / 2 ^ r + 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by norm_num) r
    have hle : j ≤ i + 2 ^ r := by omega
    calc j / 2 ^ r ≤ (i + 2 ^ r) / 2 ^ r := Nat.div_le_div_right hle
      _ = i / 2 ^ r + 1 := by rw [Nat.add_div_right _ hpos]
  have hdivtop : j / 2 ^ r ≤ 2 ^ n := by
    calc j / 2 ^ r ≤ 2 ^ (n + r) / 2 ^ r := Nat.div_le_div_right hj
      _ = 2 ^ n := by rw [Nat.pow_div (by omega) (by norm_num), Nat.add_sub_cancel]
  have hmid : edist (f (dyadicTime T n (i / 2 ^ r))) (f (dyadicTime T n (j / 2 ^ r))) ≤ e n := by
    have hbase := edist_dyadicTime_le_of_hasDyadicAdjacentBound
      (hadj n le_rfl (Nat.le_add_right n r)) hdivmono hdivtop
    refine hbase.trans ?_
    have hcount : (j / 2 ^ r - i / 2 ^ r : ℕ) ≤ 1 := by omega
    calc ((j / 2 ^ r - i / 2 ^ r : ℕ) : ℝ≥0∞) * e n ≤ (1 : ℝ≥0∞) * e n := by
          gcongr
          exact_mod_cast hcount
      _ = e n := one_mul _
  have htri : edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T (n + r) j)) ≤
      edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T n (i / 2 ^ r))) +
        (edist (f (dyadicTime T n (i / 2 ^ r))) (f (dyadicTime T n (j / 2 ^ r))) +
          edist (f (dyadicTime T n (j / 2 ^ r))) (f (dyadicTime T (n + r) j))) :=
    (edist_triangle (f (dyadicTime T (n + r) i)) (f (dyadicTime T n (i / 2 ^ r)))
        (f (dyadicTime T (n + r) j))).trans
      (add_le_add le_rfl (edist_triangle (f (dyadicTime T n (i / 2 ^ r)))
        (f (dyadicTime T n (j / 2 ^ r))) (f (dyadicTime T (n + r) j))))
  refine htri.trans ?_
  rw [edist_comm (f (dyadicTime T n (j / 2 ^ r)))]
  have hsum := add_le_add hleft (add_le_add hmid hright)
  refine hsum.trans_eq ?_
  ring
