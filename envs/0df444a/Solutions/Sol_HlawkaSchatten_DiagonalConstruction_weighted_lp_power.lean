-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.weighted_lp_power
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T20:44:38.162002+00:00
-- url     : https://prove2.me/submissions/e8229352-0436-4ce2-9b51-4d8fe35f447a

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedConvex
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lpNorm_eq_zero_iff
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_weighted_convex_hlawka
import Theorems.Thm_HlawkaSchatten_convexOn_abs_rpow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The weighted scalar estimate for arbitrary coordinate triples

The weights are the three input norms. Applying the scalar convexity
inequality coordinate by coordinate yields the dimension-independent power
estimate used to confine a hypothetical counterexample.
-/








variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]



theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _



@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']







theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]



theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))





























end HlawkaSchatten.DiagonalConstruction

theorem rpow_div_pred {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    a ^ p / a ^ (p - 1) = a := by
  by_cases h : a = 0
  · subst a
    simp [ne_of_gt (zero_lt_one.trans hp), ne_of_gt (sub_pos.mpr hp)]
  · have ha0 := lt_of_le_of_ne ha (Ne.symm h)
    rw [Real.rpow_sub ha0, Real.rpow_one]
    field_simp

theorem weighted_abs_rpow_div {a : ℝ} (ha : 0 < a) (p x : ℝ) :
    a * |x / a| ^ p = |x| ^ p / a ^ (p - 1) := by
  rw [abs_div, abs_of_pos ha, Real.div_rpow (abs_nonneg x) ha.le,
    Real.rpow_sub ha, Real.rpow_one]
  field_simp

theorem weighted_scalar_power {p a b c : ℝ} (hp : 1 < p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    |x + y| ^ p / (a + b) ^ (p - 1) +
      |x + z| ^ p / (a + c) ^ (p - 1) +
      |y + z| ^ p / (b + c) ^ (p - 1) ≤
    |x| ^ p / a ^ (p - 1) + |y| ^ p / b ^ (p - 1) + |z| ^ p / c ^ (p - 1) +
      |x + y + z| ^ p / (a + b + c) ^ (p - 1) := by
  have h := weighted_convex_hlawka (convexOn_abs_rpow hp.le) ha hb hc
    (x / a) (y / b) (z / c)
  simp only [weightedPairs, weightedTotal,
    mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ hb.ne', mul_div_cancel₀ _ hc.ne'] at h
  simpa only [weighted_abs_rpow_div ha, weighted_abs_rpow_div hb,
    weighted_abs_rpow_div hc, weighted_abs_rpow_div (add_pos ha hb),
    weighted_abs_rpow_div (add_pos ha hc), weighted_abs_rpow_div (add_pos hb hc),
    weighted_abs_rpow_div (add_pos (add_pos ha hb) hc)] using h

theorem weighted_lp_power_of_ne {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    weighted_scalar_power hp (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hy)
      (lpNorm_pos hp0 hz) (x i) (y i) (z i))
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Real.norm_eq_abs] at h
  change
    (∑ i, ‖(x + y) i‖ ^ p) / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      (∑ i, ‖(x + z) i‖ ^ p) / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      (∑ i, ‖(y + z) i‖ ^ p) / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    (∑ i, ‖x i‖ ^ p) / lpNorm p x ^ (p - 1) +
      (∑ i, ‖y i‖ ^ p) / lpNorm p y ^ (p - 1) +
      (∑ i, ‖z i‖ ^ p) / lpNorm p z ^ (p - 1) +
      (∑ i, ‖(x + y + z) i‖ ^ p) /
        (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) at h
  simpa only [← lpNorm_rpow hp0, rpow_div_pred hp (lpNorm_nonneg p x),
    rpow_div_pred hp (lpNorm_nonneg p y), rpow_div_pred hp (lpNorm_nonneg p z)] using h

theorem solution {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    lpNorm p (x + y) ^ p / (lpNorm p x + lpNorm p y) ^ (p - 1) +
      lpNorm p (x + z) ^ p / (lpNorm p x + lpNorm p z) ^ (p - 1) +
      lpNorm p (y + z) ^ p / (lpNorm p y + lpNorm p z) ^ (p - 1) ≤
    lpNorm p x + lpNorm p y + lpNorm p z +
      lpNorm p (x + y + z) ^ p / (lpNorm p x + lpNorm p y + lpNorm p z) ^ (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hx : x = 0
  · subst x
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p y),
      rpow_div_pred hp (lpNorm_nonneg p z)]
  by_cases hy : y = 0
  · subst y
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p x),
      rpow_div_pred hp (lpNorm_nonneg p z)]
    ring_nf
    rfl
  by_cases hz : z = 0
  · subst z
    simp [lpNorm_zero hp0, rpow_div_pred hp (lpNorm_nonneg p x),
      rpow_div_pred hp (lpNorm_nonneg p y)]
    ring_nf
    rfl
  exact weighted_lp_power_of_ne hp x y z hx hy hz
