-- Prove2me | solution 1 for MassEnergyEquivalence.unit_ball_inner_gap
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-30T01:11:38.466578+00:00
-- url     : https://prove2.me/submissions/557bb8cf-067c-4e06-a027-7d718ebf304f

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs

open MassEnergyEquivalence

theorem solution (x y : Vec3) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (Real.sqrt (1 - ‖x‖ ^ 2) * Real.sqrt (1 - ‖y‖ ^ 2) +
        inner ℝ x y ≤ 1) ∧
      ((Real.sqrt (1 - ‖x‖ ^ 2) * Real.sqrt (1 - ‖y‖ ^ 2) +
        inner ℝ x y = 1) ↔ x = y) := by
  let a : ℝ := Real.sqrt (1 - ‖x‖ ^ 2)
  let b : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  have hx_sq : ‖x‖ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg x) zero_le_one).2 hx
  have hy_sq : ‖y‖ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg y) zero_le_one).2 hy
  have hx_rad : 0 ≤ 1 - ‖x‖ ^ 2 := (sub_pos.mpr hx_sq).le
  have hy_rad : 0 ≤ 1 - ‖y‖ ^ 2 := (sub_pos.mpr hy_sq).le
  have ha_sq : a ^ 2 = 1 - ‖x‖ ^ 2 := by
    dsimp [a]
    exact Real.sq_sqrt hx_rad
  have hb_sq : b ^ 2 = 1 - ‖y‖ ^ 2 := by
    dsimp [b]
    exact Real.sq_sqrt hy_rad
  have hgap :
      (a - b) ^ 2 + ‖x - y‖ ^ 2 =
        2 * (1 - (a * b + inner ℝ x y)) := by
    rw [norm_sub_sq_real]
    nlinarith [ha_sq, hb_sq]
  have hnonneg : 0 ≤ (a - b) ^ 2 + ‖x - y‖ ^ 2 := by positivity
  have hle : a * b + inner ℝ x y ≤ 1 := by nlinarith [hgap]
  change (a * b + inner ℝ x y ≤ 1) ∧
    ((a * b + inner ℝ x y = 1) ↔ x = y)
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    have hnorm_sq : ‖x - y‖ ^ 2 = 0 := by
      have hab_nonneg : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
      have hxy_nonneg : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
      nlinarith [hgap]
    have hnorm : ‖x - y‖ = 0 := by
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro hxy
    subst y
    have hinner : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
    dsimp [a, b]
    rw [hinner]
    nlinarith [Real.sq_sqrt hx_rad]
