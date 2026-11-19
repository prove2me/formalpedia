-- Prove2me | solution 1 for Kyprianou.Ch01.discountedResidualVanishingAtInfinityPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:19:41.036207+00:00
-- url     : https://prove2.me/submissions/baacac45-d9ac-454c-bd44-5539492ddf0a

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
set_option autoImplicit false

/-- On any path that never crosses its upper barrier, the discounted exponential residual vanishes. -/
theorem solution
    (f : ℕ → ℝ) (x theta q : ℝ)
    (hbounded : ∀ n, f n ≤ x)
    (htheta : 0 ≤ theta) (hq : 0 < q) :
    Tendsto (fun n : ℕ => Real.exp (theta * f n - q * (n : ℝ)))
      atTop (nhds 0) := by
  let r : ℝ := Real.exp (-q)
  have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
  have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr_tend : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt
  have hc_tend : Tendsto (fun n : ℕ => Real.exp (theta * x) * r ^ n)
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hr_tend using 1 <;> simp
  have hlow (n : ℕ) :
      0 ≤ Real.exp (theta * f n - q * (n : ℝ)) :=
    (Real.exp_pos _).le
  have hhigh (n : ℕ) :
      Real.exp (theta * f n - q * (n : ℝ)) ≤
        Real.exp (theta * x) * r ^ n := by
    have hθ : theta * f n ≤ theta * x :=
      mul_le_mul_of_nonneg_left (hbounded n) htheta
    calc
      Real.exp (theta * f n - q * (n : ℝ)) ≤
          Real.exp (theta * x - q * (n : ℝ)) := by
            apply Real.exp_le_exp.mpr
            linarith
      _ = Real.exp (theta * x) * r ^ n := by
        rw [sub_eq_add_neg, Real.exp_add]
        congr 1
        dsimp [r]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc_tend hlow hhigh
