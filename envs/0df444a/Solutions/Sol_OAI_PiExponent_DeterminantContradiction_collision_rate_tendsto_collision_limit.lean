-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collision_rate_tendsto_collision_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:08:30.65205+00:00
-- url     : https://prove2.me/submissions/a3c225bd-e840-4baa-b631-24079951dfbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_row_count_asymptotic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_low_index_count_asymptotic

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hprod : (∏ i : Fin d.m, d.x (i.val + 1)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one
      (d.x_one_le (i.val + 1)))
  have hA : (d.base.A : ℝ) ≠ 0 := ne_of_gt d.base.A_pos
  have hv : (d.v0 : ℝ) ≠ 0 := ne_of_gt d.v0_pos
  have hfact : (Nat.factorial d.m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero d.m
  have hsucc : (d.m : ℝ) + 1 ≠ 0 := by positivity
  have hlow_ne :
      ((d.base.A : ℝ) ^ d.m /
        ((Nat.factorial d.m : ℝ) * ∏ i : Fin d.m, d.x (i.val + 1))) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hA) (mul_ne_zero hfact hprod)
  have hfac_succ : (Nat.factorial (d.m + 1) : ℝ) =
      ((d.m : ℝ) + 1) * (Nat.factorial d.m : ℝ) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hvalue :
      (collisionConstant * d.base.eta ^ 2) *
        ((((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) /
          ((Nat.factorial (d.m + 1) : ℝ) * (d.v0 : ℝ) *
            ∏ i : Fin d.m, d.x (i.val + 1))) /
        ((d.base.A : ℝ) ^ d.m /
          ((Nat.factorial d.m : ℝ) * ∏ i : Fin d.m, d.x (i.val + 1)))) =
        collisionLimit d := by
    rw [hfac_succ]
    unfold collisionLimit
    field_simp [hprod, hfact, hA, hv, hsucc] <;> ring
  have hlim := ((row_count_asymptotic d).div
    (low_index_count_asymptotic d) hlow_ne).const_mul
      (collisionConstant * d.base.eta ^ 2)
  rw [hvalue] at hlim
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (collisionConstant * d.base.eta ^ 2) *
      (((actualRowCount d H : ℝ) / H ^ (d.m + 1)) /
        ((lowIndexCount d H : ℝ) / H ^ d.m)) = collisionRate d H
  unfold collisionRate
  have hH0 : H ≠ 0 := ne_of_gt hH
  by_cases hl : (lowIndexCount d H : ℝ) = 0
  · simp [hl]
  · rw [pow_succ H d.m]
    field_simp [hH0, hl] <;> ring
