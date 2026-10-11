-- Prove2me | solution 1 for HunterPDE.Newtonian.fundamentalSolution_sphere_flux
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:51:28.237461+00:00
-- url     : https://prove2.me/submissions/2cfbdf9a-b375-4354-8fe7-b17d1511e7c6

import Theorems.Thm_MeasureTheory_integral_sphere_coordinate_mul
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open MeasureTheory HunterPDE.Newtonian
theorem solution (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R) (i j : Fin n) :
    R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere) =
      1 / (n : ℝ) * (if i = j then 1 else 0) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn0)
  have hα : unitBallVolume n ≠ 0 := by
    apply ne_of_gt
    unfold unitBallVolume
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'
      (measure_ball_lt_top.ne)
  have hpoint (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j =
        (1 / ((n : ℝ) * unitBallVolume n) / R ^ (n - 1)) * (w.1 i * w.1 j) := by
    have hw : ‖w.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.2
    have hnorm : ‖-(R • w.1)‖ = R := by simp [norm_smul, abs_of_pos hR, hw]
    have hne : -(R • w.1) ≠ 0 := by
      intro he
      have : R = 0 := by simpa [he] using hnorm.symm
      exact hR.ne' this
    rw [(fundamentalSolution_partial n hn).2 _ hne i, hnorm]
    simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hR.ne']
    <;> ring
  have hflux : R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere) =
      1 / (n : ℝ) * (if i = j then 1 else 0) := by
    simp_rw [hpoint]
    rw [integral_const_mul, integral_sphere_coordinate_mul n hn0 i j]
    field_simp [hα, hnr, hR.ne']
    <;> ring
  exact hflux
