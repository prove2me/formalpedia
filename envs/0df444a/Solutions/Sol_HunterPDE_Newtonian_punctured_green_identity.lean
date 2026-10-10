-- Prove2me | solution 1 for HunterPDE.Newtonian.punctured_green_identity
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:20:21.563985+00:00
-- url     : https://prove2.me/submissions/ca7778b1-9b3e-48cd-8703-e96683083355

import Theorems.Thm_MeasureTheory_exterior_green_of_coulomb_gradient
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set Topology
open scoped ContDiff
open Laplacian
open HunterPDE.Newtonian HunterPDE.Harmonic

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) (r : ℝ) (hr : 0 < r) :
    (∫ y in (Metric.ball x r)ᶜ, fundamentalSolution n (x - y) * (Δ f) y) =
      -fundamentalSolution n (r • v) * (∫ y in Metric.ball x r, (Δ f) y) -
        sphereAverage f x r := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hα : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact ENNReal.toReal_ne_zero.mpr ⟨
      (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne',
      measure_ball_lt_top.ne⟩
  have hnorm : ‖r • v‖ = r := by
    simp [norm_smul, hv, Real.norm_eq_abs, abs_of_pos hr]
  have hκ : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ = r →
      fundamentalSolution n z = fundamentalSolution n (r • v) := by
    intro z hz
    simp only [fundamentalSolution, hz, hnorm]
  have h := MeasureTheory.exterior_green_of_coulomb_gradient n hn
    (fundamentalSolution n) (fundamentalSolution_partial n hn).1
    (-(1 / ((n : ℝ) * unitBallVolume n)))
    (fun z hz i => (fundamentalSolution_partial n hn).2 z hz i)
    f hf hfc x r hr (fundamentalSolution n (r • v)) hκ
  have hc : (n : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
      (-(1 / ((n : ℝ) * unitBallVolume n))) = -1 := by
    change (n : ℝ) * unitBallVolume n * (-(1 / ((n : ℝ) * unitBallVolume n))) = -1
    field_simp [hnR, hα]
  rw [hc] at h
  simpa only [neg_one_mul, sub_eq_add_neg] using h
