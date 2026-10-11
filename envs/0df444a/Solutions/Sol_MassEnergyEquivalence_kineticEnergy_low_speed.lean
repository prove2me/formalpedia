-- Prove2me | solution 1 for MassEnergyEquivalence.kineticEnergy_low_speed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:15:22.69327+00:00
-- url     : https://prove2.me/submissions/50c7ff9e-767e-46e8-b9cc-0f4a8f064b9c

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- Uniform fourth-order remainder bound for relativistic kinetic energy near rest. -/
theorem solution (c m : ℝ) (hc : 0 < c) (hm : 0 ≤ m) :
    (fun v : Vec3 => kineticEnergy c m v - 1 / 2 * m * ‖v‖ ^ 2) =O[𝓝 0]
      (fun v : Vec3 => ‖v‖ ^ 4) := by
  have hcn : 0 < c ^ 2 := sq_pos_of_pos hc
  have hrad : 0 < c / 2 := by positivity
  apply Asymptotics.IsBigO.of_bound (3 * m / c ^ 2)
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
  have hdenp : 0 < 2 * s * (1 + s) ^ 2 := by positivity
  have hden : 1 ≤ 2 * s * (1 + s) ^ 2 := by
    have ha : 1 ≤ 2 * s := by linarith
    have hb : 1 ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * s) * (1 + s) ^ 2 :=
        mul_le_mul ha hb (by norm_num) (by linarith)
  have hqroot : q = 1 - s ^ 2 := by linarith [hroot]
  have hid :
      (1 / s - 1 - q / 2) * (2 * s * (1 + s) ^ 2) =
        q ^ 2 * (s + 2) := by
    rw [hqroot]
    field_simp [ne_of_gt hs]
    ring
  have hepos : 0 ≤ 1 / s - 1 - q / 2 := by
    by_contra hn
    have hneg : 1 / s - 1 - q / 2 < 0 := lt_of_not_ge hn
    have hprod : (1 / s - 1 - q / 2) *
        (2 * s * (1 + s) ^ 2) < 0 :=
      mul_neg_of_neg_of_pos hneg hdenp
    have hright : 0 ≤ q ^ 2 * (s + 2) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith [hid]
  have heupper : 1 / s - 1 - q / 2 ≤ 3 * q ^ 2 := by
    have ha : 0 ≤
        (1 / s - 1 - q / 2) * (2 * s * (1 + s) ^ 2 - 1) :=
      mul_nonneg hepos (by linarith)
    have hb : q ^ 2 * (s + 2) ≤ 3 * q ^ 2 := by
      have hh : 0 ≤ q ^ 2 * (1 - s) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith
    nlinarith [hid]
  have herror :
      kineticEnergy c m v - 1 / 2 * m * ‖v‖ ^ 2 =
        (m * c ^ 2) * (1 / s - 1 - q / 2) := by
    change ((1 / s * m * c ^ 2 - m * c ^ 2) -
      1 / 2 * m * r ^ 2) =
      (m * c ^ 2) * (1 / s - 1 - q / 2)
    dsimp [q]
    field_simp [ne_of_gt hcn, ne_of_gt hs]
  have hcscale : 0 ≤ m * c ^ 2 :=
    mul_nonneg hm (le_of_lt hcn)
  have hbound :
      |kineticEnergy c m v - 1 / 2 * m * ‖v‖ ^ 2| ≤
        (3 * m / c ^ 2) * ‖v‖ ^ 4 := by
    rw [herror, abs_mul, abs_of_nonneg hcscale,
      abs_of_nonneg hepos]
    calc
      m * c ^ 2 * (1 / s - 1 - q / 2) ≤
        m * c ^ 2 * (3 * q ^ 2) :=
        mul_le_mul_of_nonneg_left heupper hcscale
      _ = (3 * m / c ^ 2) * ‖v‖ ^ 4 := by
        dsimp [q, r]
        field_simp [ne_of_gt hcn]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg v) 4)] using hbound
