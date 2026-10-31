-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:03:59.434619+00:00
-- url     : https://prove2.me/submissions/6c968e9e-eec2-4cf3-8989-a516505495a1

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicIncrements_eff99a2c
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
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
* `MarkovProcess.p2m_inline_edist_dyadicTime_ancestor_le`, the bound from a fine subdivision point to its
  canonical coarse ancestor by the sum of the intervening bounds;
* `MarkovProcess.p2m_inline_edist_dyadicTime_le_of_sub_le`, the two-point chaining bound: subdivision points
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









theorem dist_dyadicTime (T : ℝ≥0) (m i j : ℕ) :
    dist (dyadicTime T m i) (dyadicTime T m j) = (T : ℝ) * |(i : ℝ) - j| / 2 ^ m := by
  rw [NNReal.dist_eq, dyadicTime_coe, dyadicTime_coe, div_sub_div_same, ← mul_sub, abs_div,
    abs_mul, abs_of_nonneg T.coe_nonneg, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m)]

theorem edist_dyadicTime_succ_le (T : ℝ≥0) (m i : ℕ) :
    edist (dyadicTime T m i) (dyadicTime T m (i + 1)) ≤ ((T / 2 ^ m : ℝ≥0) : ℝ≥0∞) := by
  rw [edist_dist]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [ENNReal.coe_toReal, dist_dyadicTime]
  push_cast
  rw [show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring, abs_neg, abs_one, mul_one]

end Subdivision

section Chaining

variable {E : Type*} [PseudoEMetricSpace E]











end Chaining

section Approximation



theorem dyadicIndex_le {T : ℝ≥0} (hT : 0 < T) {s : ℝ≥0} (hs : s ≤ T) (m : ℕ) :
    dyadicIndex T m s ≤ 2 ^ m := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hs' : (s : ℝ) ≤ (T : ℝ) := hs
  have hbound : (s : ℝ) * 2 ^ m / T ≤ ((2 ^ m : ℕ) : ℝ) := by
    rw [div_le_iff₀ hT']
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  calc dyadicIndex T m s ≤ ⌊((2 ^ m : ℕ) : ℝ)⌋₊ := Nat.floor_mono hbound
    _ = 2 ^ m := Nat.floor_natCast _

theorem dyadicIndex_mono {T : ℝ≥0} (hT : 0 < T) (m : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    dyadicIndex T m s ≤ dyadicIndex T m t := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hst' : (s : ℝ) ≤ (t : ℝ) := hst
  exact Nat.floor_mono (by gcongr)









end Approximation

end MarkovProcess


open Filter Topology
open scoped ENNReal NNReal
namespace MarkovProcess
variable {E : Type*} [PseudoEMetricSpace E]

private theorem p2m_inline_dyadicTime_succ_level (T : ℝ≥0) (m i : ℕ) :
    dyadicTime T (m + 1) (2 * i) = dyadicTime T m i := by
  rw [← NNReal.coe_inj, dyadicTime_coe, dyadicTime_coe]
  push_cast
  rw [pow_succ]
  field_simp

private theorem p2m_inline_edist_dyadicTime_le_of_hasDyadicAdjacentBound {f : ℝ≥0 → E} {T : ℝ≥0} {m : ℕ}
    {e : ℝ≥0∞} (hf : HasDyadicAdjacentBound f T m e) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ m) :
    edist (f (dyadicTime T m i)) (f (dyadicTime T m j)) ≤ (j - i : ℕ) * e := by
  have hchain := edist_le_Ico_sum_of_edist_le (f := fun k ↦ f (dyadicTime T m k)) hij
    (d := fun _ ↦ e) (fun {k} _ hkj ↦ hf k (lt_of_lt_of_le hkj hj))
  simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using hchain

private theorem p2m_inline_edist_dyadicTime_parent_le {f : ℝ≥0 → E} {T : ℝ≥0} {m : ℕ} {e : ℝ≥0∞}
    (hf : HasDyadicAdjacentBound f T (m + 1) e) {i : ℕ} (hi : i ≤ 2 ^ (m + 1)) :
    edist (f (dyadicTime T (m + 1) i)) (f (dyadicTime T m (i / 2))) ≤ e := by
  rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
  · have hval : 2 * (i / 2) = i := by omega
    rw [← p2m_inline_dyadicTime_succ_level T m (i / 2), hval, edist_self]
    exact zero_le
  · have hval : 2 * (i / 2) + 1 = i := by omega
    have hlt : 2 * (i / 2) < 2 ^ (m + 1) := by omega
    have hbound := hf (2 * (i / 2)) hlt
    rw [hval] at hbound
    rw [← p2m_inline_dyadicTime_succ_level T m (i / 2), edist_comm]
    exact hbound

private theorem p2m_inline_edist_dyadicTime_ancestor_le {f : ℝ≥0 → E} {T : ℝ≥0} {e : ℕ → ℝ≥0∞} {n : ℕ} :
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
        p2m_inline_edist_dyadicTime_parent_le (hadj (n + r + 1) (by omega) (by omega)) hi'
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

private theorem p2m_inline_dyadicTime_dyadicIndex_le {T : ℝ≥0} (hT : 0 < T) (m : ℕ) (s : ℝ≥0) :
    dyadicTime T m (dyadicIndex T m s) ≤ s := by
  have hT' : (0 : ℝ) < (T : ℝ) := hT
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hx0 : (0 : ℝ) ≤ (s : ℝ) * 2 ^ m / T := by positivity
  have hfloor : ((dyadicIndex T m s : ℕ) : ℝ) ≤ (s : ℝ) * 2 ^ m / T := Nat.floor_le hx0
  rw [← NNReal.coe_le_coe, dyadicTime_coe, div_le_iff₀ hpow]
  calc (T : ℝ) * ((dyadicIndex T m s : ℕ) : ℝ) ≤ (T : ℝ) * ((s : ℝ) * 2 ^ m / T) :=
        mul_le_mul_of_nonneg_left hfloor T.coe_nonneg
    _ = (s : ℝ) * 2 ^ m := by field_simp

private theorem p2m_inline_le_dyadicTime_dyadicIndex_add {T : ℝ≥0} (hT : 0 < T) (m : ℕ) (s : ℝ≥0) :
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

private theorem p2m_inline_edist_dyadicTime_le_of_sub_le {f : ℝ≥0 → E} {T : ℝ≥0} {e : ℕ → ℝ≥0∞} {n r : ℕ}
    (hadj : ∀ k, n ≤ k → k ≤ n + r → HasDyadicAdjacentBound f T k (e k))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2 ^ (n + r)) (hsub : j - i ≤ 2 ^ r) :
    edist (f (dyadicTime T (n + r) i)) (f (dyadicTime T (n + r) j)) ≤
      2 * (∑ s ∈ Finset.range r, e (n + s + 1)) + e n := by
  have hi : i ≤ 2 ^ (n + r) := hij.trans hj
  have hanc := fun (k : ℕ) (hk : n < k) (hk' : k ≤ n + r) ↦ hadj k hk.le hk'
  have hleft := p2m_inline_edist_dyadicTime_ancestor_le (f := f) (T := T) (e := e) (n := n) r hanc i hi
  have hright := p2m_inline_edist_dyadicTime_ancestor_le (f := f) (T := T) (e := e) (n := n) r hanc j hj
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
    have hbase := p2m_inline_edist_dyadicTime_le_of_hasDyadicAdjacentBound
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

private theorem p2m_inline_tendsto_dyadicTime_dyadicIndex {T : ℝ≥0} (hT : 0 < T) (s : ℝ≥0) :
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
    p2m_inline_dyadicTime_dyadicIndex_le hT m s
  have h2 : (s : ℝ) ≤ ((dyadicTime T m (dyadicIndex T m s) : ℝ≥0) : ℝ) + (T : ℝ) / 2 ^ m := by
    have h := NNReal.coe_le_coe.mpr (p2m_inline_le_dyadicTime_dyadicIndex_add hT m s)
    push_cast at h
    exact h
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

private theorem p2m_inline_dyadicIndex_sub_le {T : ℝ≥0} (hT : 0 < T) {s t : ℝ≥0} {n r : ℕ}
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
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoEMetricSpace alpha]



theorem modulusSet_mono {T : ℝ≥0} {delta r r' : ℝ≥0∞} (hrr : r ≤ r') :
    modulusSet (alpha := alpha) T delta r ⊆ modulusSet T delta r' :=
  fun _ homega s t hs ht hd ↦ (homega s t hs ht hd).trans hrr





end ContinuousPath

section Estimate

variable {alpha : Type*} [PseudoEMetricSpace alpha]

/-- The chaining bound produced at base level `N`: twice the exact geometric tail above `N` plus
one coarse threshold. -/
private noncomputable def dyadicChainBound (gamma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  2 * (dyadicIncrementThreshold gamma (N + 1) *
      (1 - dyadicIncrementThresholdRatio gamma)⁻¹) + dyadicIncrementThreshold gamma N

private theorem tendsto_dyadicChainBound {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (dyadicChainBound gamma) atTop (nhds 0) := by
  have htail := p2m_embedded_5e87c01d6b0fde4a hgamma
  have hthr : Tendsto (fun N : ℕ ↦ dyadicIncrementThreshold gamma N) atTop (nhds 0) := by
    simp_rw [dyadicIncrementThreshold_eq_ratio_pow]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (dyadicIncrementThresholdRatio_lt_one hgamma)
  have hdouble : Tendsto (fun N : ℕ ↦ 2 * (dyadicIncrementThreshold gamma (N + 1) *
      (1 - dyadicIncrementThresholdRatio gamma)⁻¹)) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr (by simp))
  simpa only [dyadicChainBound, add_zero] using! hdouble.add hthr

/-- The event that some adjacent increment of the level-`n` subdivision of `[0, T]` reaches the
level's Kolmogorov--Chentsov threshold. -/
private def badLevel (T : ℝ≥0) (p gamma : ℝ) (n : ℕ) : Set (ContinuousPath alpha) :=
  finiteGridBadIncrement (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t)
    (fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) p (dyadicIncrementThreshold gamma n)

private theorem coe_div_two_pow (T : ℝ≥0) (n : ℕ) :
    ((T / 2 ^ n : ℝ≥0) : ℝ≥0∞) = (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ENNReal.coe_div (by positivity), div_eq_mul_inv, ENNReal.coe_pow, ENNReal.coe_ofNat]

private theorem measure_badLevel_le {p q : ℝ} {M : ℝ≥0} {mu : Measure (ContinuousPath alpha)}
    (hX : IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t) mu p q M)
    {gamma : ℝ} (hgamma : 0 < gamma) (T : ℝ≥0) (n : ℕ) :
    mu (badLevel T p gamma n) ≤
      (T : ℝ≥0∞) ^ q * ((M * dyadicIncrementDecayRatio p q gamma ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hgrid : ∀ i : Fin (2 ^ n),
      edist ((fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) i.castSucc)
          ((fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) i.succ) ≤
        ((T / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    intro i
    simpa only [Fin.val_castSucc, Fin.val_succ] using edist_dyadicTime_succ_le T n (i : ℕ)
  have hbound := IsKolmogorovProcess.p2m_embedded_f2e9b915d032a86f hX
    (fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) _ _ hgrid
    (dyadicIncrementThreshold_ne_zero hgamma n) (dyadicIncrementThreshold_ne_top hgamma n)
  refine hbound.trans (le_of_eq ?_)
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [coe_div_two_pow, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top (by simp),
    ← p2m_embedded_733eeb3a103a07ee p q gamma M n]
  simp only [div_eq_mul_inv]
  ring

private theorem le_add_of_edist_le {s t c : ℝ≥0} (h : edist s t ≤ (c : ℝ≥0∞)) : t ≤ s + c := by
  have hd : dist s t ≤ (c : ℝ) := by
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff c.coe_nonneg).mp h
  rw [NNReal.dist_eq] at hd
  have hlow := (abs_le.mp hd).1
  rw [← NNReal.coe_le_coe]
  push_cast
  linarith

private theorem mem_modulusSet_of_notMem_badLevel {p gamma : ℝ} (hp : 0 < p)
    {T : ℝ≥0} (hT : 0 < T) (N : ℕ) {omega : ContinuousPath alpha}
    (homega : ∀ n, N ≤ n → omega ∉ badLevel T p gamma n) :
    omega ∈ ContinuousPath.modulusSet T ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞)
      (dyadicChainBound gamma N) := by
  have hadj : ∀ n, N ≤ n →
      HasDyadicAdjacentBound (fun t ↦ omega t) T n (dyadicIncrementThreshold gamma n) := by
    intro n hn i hi
    have hlt := edist_adjacent_lt_of_notMem_finiteGridBadIncrement
      (X := fun (t : ℝ≥0) (eta : ContinuousPath alpha) ↦ eta t)
      (grid := fun i : Fin (2 ^ n + 1) ↦ dyadicTime T n (i : ℕ)) hp (homega n hn)
      (⟨i, hi⟩ : Fin (2 ^ n))
    simpa only [Fin.val_castSucc, Fin.val_succ] using hlt.le
  have key : ∀ s t : ℝ≥0, s ≤ T → t ≤ T → s ≤ t →
      edist s t ≤ ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞) →
        edist (omega s) (omega t) ≤ dyadicChainBound gamma N := by
    intro s t hs ht hst hd
    have hd' : t ≤ s + T / 2 ^ (N + 1) := le_add_of_edist_le hd
    have hstep : ∀ u : ℕ,
        edist (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) s)))
          (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) t))) ≤
        dyadicChainBound gamma N := by
      intro u
      have hj := dyadicIndex_le hT ht (N + (u + 1))
      have hij := dyadicIndex_mono hT (N + (u + 1)) hst
      have hsub := p2m_inline_dyadicIndex_sub_le (T := T) hT (n := N) (r := u + 1) (Nat.le_add_left 1 u) hd'
      have hchain := p2m_inline_edist_dyadicTime_le_of_sub_le (f := fun v ↦ omega v) (T := T)
        (e := dyadicIncrementThreshold gamma) (n := N) (r := u + 1)
        (fun k hk _ ↦ hadj k hk) hij hj hsub
      refine hchain.trans ?_
      unfold dyadicChainBound
      gcongr
      exact sum_dyadicIncrementThreshold_ancestor_le_tail gamma N (u + 1)
    have hlevel : Tendsto (fun u : ℕ ↦ N + (u + 1)) atTop atTop :=
      tendsto_atTop_mono (fun u ↦ by simp only [id_eq]; omega) tendsto_id
    have htends : Tendsto
        (fun u : ℕ ↦ edist (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) s)))
          (omega (dyadicTime T (N + (u + 1)) (dyadicIndex T (N + (u + 1)) t))))
        atTop (nhds (edist (omega s) (omega t))) := by
      refine Tendsto.edist ?_ ?_
      · exact (omega.continuous.tendsto s).comp
          ((p2m_inline_tendsto_dyadicTime_dyadicIndex hT s).comp hlevel)
      · exact (omega.continuous.tendsto t).comp
          ((p2m_inline_tendsto_dyadicTime_dyadicIndex hT t).comp hlevel)
    exact le_of_tendsto htends (Eventually.of_forall hstep)
  intro s t hs ht hd
  rcases le_total s t with hst | hst
  · exact key s t hs ht hst hd
  · rw [edist_comm]
    exact key t s ht hs hst (by rwa [edist_comm])

private theorem tendsto_badTail {p q gamma : ℝ} (hp : 0 < p) (hgamma : 0 < gamma)
    (hgammaq : gamma < (q - 1) / p) (M T : ℝ≥0) :
    Tendsto (fun N : ℕ ↦ (T : ℝ≥0∞) ^ q *
        ∑' k : ℕ, ((M * dyadicIncrementDecayRatio p q gamma ^ (N + k) : ℝ≥0) : ℝ≥0∞))
      atTop (nhds 0) := by
  set rho : ℝ≥0 := dyadicIncrementDecayRatio p q gamma with hrhodef
  have hrho : (rho : ℝ≥0∞) < 1 := by
    exact_mod_cast dyadicIncrementDecayRatio_lt_one hp hgammaq
  have hsum : ∀ N : ℕ, (∑' k : ℕ, ((M * rho ^ (N + k) : ℝ≥0) : ℝ≥0∞)) =
      (M : ℝ≥0∞) * ((rho : ℝ≥0∞) ^ N * (1 - (rho : ℝ≥0∞))⁻¹) := by
    intro N
    have hrw : ∀ k : ℕ, ((M * rho ^ (N + k) : ℝ≥0) : ℝ≥0∞) =
        (M : ℝ≥0∞) * ((rho : ℝ≥0∞) ^ N * (rho : ℝ≥0∞) ^ k) := by
      intro k
      push_cast
      rw [pow_add]
    simp_rw [hrw]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hpow : Tendsto (fun N : ℕ ↦ ((rho : ℝ≥0∞)) ^ N) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrho
  have hq : 0 < q := by
    have hpos : 0 < (q - 1) / p := lt_trans hgamma hgammaq
    have := (div_pos_iff_of_pos_right hp).mp hpos
    linarith
  have hfinite : (T : ℝ≥0∞) ^ q * (M : ℝ≥0∞) * (1 - (rho : ℝ≥0∞))⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ?_
    · exact ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.coe_ne_top
    · exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hrho).ne'
  have hconst : Tendsto (fun N : ℕ ↦ ((T : ℝ≥0∞) ^ q * (M : ℝ≥0∞) * (1 - (rho : ℝ≥0∞))⁻¹) *
      ((rho : ℝ≥0∞)) ^ N) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hpow (Or.inr hfinite)
  refine hconst.congr fun N ↦ ?_
  rw [hsum N]
  ring



end Estimate

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal




variable {alpha : Type*} [PseudoEMetricSpace alpha]

















namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath

theorem solution {p q : ℝ} {M : ℝ≥0} {gamma : ℝ}
    (hp : 0 < p) (hgamma : 0 < gamma) (hgammaq : gamma < (q - 1) / p) (T : ℝ≥0) {r : ℝ≥0∞}
    (hr : 0 < r) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧
      ∀ mu : Measure (ContinuousPath alpha),
        IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t) mu p q M →
          mu (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT | hT
  · refine ⟨1, one_pos, fun mu _ ↦ ?_⟩
    have hempty : (ContinuousPath.modulusSet (alpha := alpha) T 1 r)ᶜ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro omega homega
      refine homega fun s t hs ht _ ↦ ?_
      have hs0 : s = 0 := le_antisymm (hT ▸ hs) (zero_le : (0 : ℝ≥0) ≤ s)
      have ht0 : t = 0 := le_antisymm (hT ▸ ht) (zero_le : (0 : ℝ≥0) ≤ t)
      subst hs0
      subst ht0
      simp
    rw [hempty]
    simp
  · have hchain := (tendsto_dyadicChainBound hgamma).eventually_le_const hr
    have htail := (tendsto_badTail hp hgamma hgammaq M T).eventually_le_const heps
    obtain ⟨N, hN1, hN2⟩ := (hchain.and htail).exists
    refine ⟨((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞), ?_, fun mu hX ↦ ?_⟩
    · exact_mod_cast div_pos hT (by positivity)
    · have hsubset : (ContinuousPath.modulusSet (alpha := alpha) T
          ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞) r)ᶜ ⊆
            ⋃ k : ℕ, badLevel T p gamma (N + k) := by
        intro omega homega
        by_contra hcon
        refine homega (ContinuousPath.modulusSet_mono hN1 ?_)
        refine mem_modulusSet_of_notMem_badLevel hp hT N fun n hn hmem ↦ ?_
        exact hcon (Set.mem_iUnion.mpr ⟨n - N, by rwa [Nat.add_sub_cancel' hn]⟩)
      calc mu (ContinuousPath.modulusSet T ((T / 2 ^ (N + 1) : ℝ≥0) : ℝ≥0∞) r)ᶜ
          ≤ mu (⋃ k : ℕ, badLevel T p gamma (N + k)) := measure_mono hsubset
        _ ≤ ∑' k : ℕ, mu (badLevel T p gamma (N + k)) := measure_iUnion_le _
        _ ≤ ∑' k : ℕ, (T : ℝ≥0∞) ^ q *
              ((M * dyadicIncrementDecayRatio p q gamma ^ (N + k) : ℝ≥0) : ℝ≥0∞) :=
            ENNReal.tsum_le_tsum fun k ↦ measure_badLevel_le hX hgamma T (N + k)
        _ = (T : ℝ≥0∞) ^ q *
              ∑' k : ℕ, ((M * dyadicIncrementDecayRatio p q gamma ^ (N + k) : ℝ≥0) : ℝ≥0∞) :=
            ENNReal.tsum_mul_left
        _ ≤ eps := hN2
