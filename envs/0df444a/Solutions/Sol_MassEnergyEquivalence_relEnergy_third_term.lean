-- Prove2me | solution 1 for MassEnergyEquivalence.relEnergy_third_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:28:27.557211+00:00
-- url     : https://prove2.me/submissions/d65f4261-3b16-4298-9b04-9e41fd1db7ae

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- The third binomial term leaves a sixth-order remainder near zero velocity. -/
theorem solution (c m : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    (fun v : Vec3 => relEnergy c m v -
      (m * c ^ 2 + 1 / 2 * m * ‖v‖ ^ 2 *
        (1 + 3 * ‖v‖ ^ 2 / (4 * c ^ 2)))) =O[𝓝 0]
      (fun v : Vec3 => ‖v‖ ^ 6) := by
  have hcn : 0 < c ^ 2 := sq_pos_of_pos hc
  have hrad : 0 < c / 2 := by positivity
  apply Asymptotics.IsBigO.of_bound (5 * m / c ^ 4)
  filter_upwards [Metric.ball_mem_nhds (0 : Vec3) hrad] with v hv
  have hvsmall : ‖v‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hv
  let r : ℝ := ‖v‖
  let q : ℝ := r ^ 2 / c ^ 2
  let s : ℝ := Real.sqrt (1 - q)
  have hr : 0 ≤ r := norm_nonneg _
  have hrhalf : r ≤ c / 2 := le_of_lt hvsmall
  have hrr : r ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrhalf)
      (add_nonneg (le_of_lt hrad) hr)]
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) (le_of_lt hcn)
  have hqquarter : q ≤ 1 / 4 := by
    dsimp [q]
    apply (div_le_iff₀ hcn).2
    nlinarith [hrr]
  have ht : 0 < 1 - q := by linarith
  have hroot : s ^ 2 = 1 - q := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt ht)
  have hs : 0 < s := Real.sqrt_pos.2 ht
  have hsupper : s ≤ 1 := by
    have hh : s ^ 2 ≤ 1 := by linarith
    nlinarith
  have hshalf : 1 / 2 ≤ s := by
    have hh : 3 / 4 ≤ s ^ 2 := by linarith
    nlinarith
  have hsp : 0 < 1 + s := by linarith
  have hdenp : 0 < 8 * s * (1 + s) ^ 3 := by positivity
  have hpow : 1 ≤ (1 + s) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg s) (le_of_lt hs)]
  have hden : 4 ≤ 8 * s * (1 + s) ^ 3 := by
    have ha : 4 ≤ 8 * s := by linarith
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ ≤ (8 * s) * (1 + s) ^ 3 :=
        mul_le_mul ha hpow (by norm_num) (by positivity)
  have hqroot : q = 1 - s ^ 2 := by linarith [hroot]
  have hid :
      (1 / s - 1 - q / 2 - 3 * q ^ 2 / 8) *
        (8 * s * (1 + s) ^ 3) =
      q ^ 3 * (3 * s ^ 2 + 9 * s + 8) := by
    rw [hqroot]
    field_simp [ne_of_gt hs]
    ring
  have hepos : 0 ≤ 1 / s - 1 - q / 2 - 3 * q ^ 2 / 8 := by
    by_contra hn
    have hneg : 1 / s - 1 - q / 2 - 3 * q ^ 2 / 8 < 0 :=
      lt_of_not_ge hn
    have hh : (1 / s - 1 - q / 2 - 3 * q ^ 2 / 8) *
        (8 * s * (1 + s) ^ 3) < 0 :=
      mul_neg_of_neg_of_pos hneg hdenp
    have hp : 0 ≤ 3 * s ^ 2 + 9 * s + 8 := by positivity
    have hp0 : 0 ≤ q ^ 3 * (3 * s ^ 2 + 9 * s + 8) :=
      mul_nonneg (pow_nonneg hq 3) hp
    linarith [hid]
  have hpoly : 3 * s ^ 2 + 9 * s + 8 ≤ 20 := by
    have hs2 : s ^ 2 ≤ 1 := by linarith [hroot]
    nlinarith
  have heupper : 1 / s - 1 - q / 2 - 3 * q ^ 2 / 8 ≤ 5 * q ^ 3 := by
    have ha : 0 ≤
        (1 / s - 1 - q / 2 - 3 * q ^ 2 / 8) *
        (8 * s * (1 + s) ^ 3 - 4) :=
      mul_nonneg hepos (by linarith)
    have hb :
        q ^ 3 * (3 * s ^ 2 + 9 * s + 8) ≤ 20 * q ^ 3 := by
      nlinarith [mul_nonneg (pow_nonneg hq 3)
        (sub_nonneg.mpr hpoly)]
    nlinarith [hid]
  have herror :
      relEnergy c m v -
        (m * c ^ 2 + 1 / 2 * m * ‖v‖ ^ 2 *
          (1 + 3 * ‖v‖ ^ 2 / (4 * c ^ 2))) =
      (m * c ^ 2) * (1 / s - 1 - q / 2 - 3 * q ^ 2 / 8) := by
    change (1 / s * m * c ^ 2 -
        (m * c ^ 2 + 1 / 2 * m * r ^ 2 *
          (1 + 3 * r ^ 2 / (4 * c ^ 2)))) =
      m * c ^ 2 * (1 / s - 1 - q / 2 - 3 * q ^ 2 / 8)
    dsimp [q]
    field_simp [ne_of_gt hcn, ne_of_gt hs]
    ring
  have hcscale : 0 ≤ m * c ^ 2 :=
    mul_nonneg hm (le_of_lt hcn)
  have hbound :
      |relEnergy c m v -
        (m * c ^ 2 + 1 / 2 * m * ‖v‖ ^ 2 *
          (1 + 3 * ‖v‖ ^ 2 / (4 * c ^ 2)))| ≤
        (5 * m / c ^ 4) * ‖v‖ ^ 6 := by
    rw [herror, abs_mul, abs_of_nonneg hcscale,
      abs_of_nonneg hepos]
    calc
      m * c ^ 2 * (1 / s - 1 - q / 2 - 3 * q ^ 2 / 8) ≤
        m * c ^ 2 * (5 * q ^ 3) :=
        mul_le_mul_of_nonneg_left heupper hcscale
      _ = (5 * m / c ^ 4) * ‖v‖ ^ 6 := by
        dsimp [q, r]
        field_simp [ne_of_gt hc]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg v) 6)] using hbound
