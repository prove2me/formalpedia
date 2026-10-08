-- Prove2me | solution 1 for MazurReduction.leading_coefficient_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T10:15:38.254479+00:00
-- url     : https://prove2.me/submissions/261f5ad4-61d5-40f5-aa89-c734689e2253

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib
open Polynomial

theorem solution
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : K[X]) {x : K}
    (hd : 0 < f.natDegree) (hc : ∀ i, v (f.coeff i) ≤ 1)
    (hr : f.eval x = 0) (hx : 1 < v x) :
    v f.leadingCoeff * v x ≤ 1 := by
  by_contra hn
  have hn' : 1 < v f.leadingCoeff * v x := lt_of_not_ge hn
  have hxpos : 0 < v x := zero_lt_one.trans hx
  have hlcpos : 0 < v f.leadingCoeff := by
    by_contra h
    have hz : v f.leadingCoeff = 0 := le_antisymm (le_of_not_gt h) zero_le
    simp [hz] at hn'
  have htoppos : 0 < v f.leadingCoeff * v x ^ f.natDegree :=
    mul_pos hlcpos (pow_pos hxpos _)
  have hstep : v x ^ (f.natDegree - 1) < v f.leadingCoeff * v x ^ f.natDegree := by
    have he : f.natDegree = (f.natDegree - 1) + 1 := by omega
    calc
      v x ^ (f.natDegree - 1) = 1 * v x ^ (f.natDegree - 1) := (one_mul _).symm
      _ < (v f.leadingCoeff * v x) * v x ^ (f.natDegree - 1) :=
        mul_lt_mul_of_pos_right hn' (pow_pos hxpos _)
      _ = v f.leadingCoeff * v x ^ f.natDegree := by
        conv_rhs => rw [he, pow_add, pow_one]
        ac_rfl
  rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at hr
  apply_fun v at hr
  have hlt := v.map_sum_lt (s := Finset.range f.natDegree) htoppos.ne' (fun i hi => show
      v (f.coeff i * x ^ i) < v f.leadingCoeff * v x ^ f.natDegree from by
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left zero_le (hc i)).trans_lt
      ((pow_le_pow_right₀ hx.le (by have := Finset.mem_range.mp hi; omega)).trans_lt hstep))
  exact (ne_of_lt hlt) (by simpa only [v.map_neg, map_mul, map_pow] using hr)
