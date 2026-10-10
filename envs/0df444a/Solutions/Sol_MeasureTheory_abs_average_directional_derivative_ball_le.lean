-- Prove2me | solution 1 for MeasureTheory.abs_average_directional_derivative_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T14:59:52.2032+00:00
-- url     : https://prove2.me/submissions/df92d1bb-6ac0-4c45-8a33-de253045bae5

import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory Set
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hf : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) {M : ℝ}
    (hM : ∀ y ∈ Metric.closedBall x r, |f y| ≤ M) :
    |⨍ y in Metric.ball x r, fderiv ℝ f y v| ≤ (n / r) * M * ‖v‖ := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  have hMn : 0 ≤ M := (abs_nonneg (f x)).trans (hM x (Metric.mem_closedBall_self hr.le))
  have hb : ∀ ω : S, ‖f (x + r • ω.1) * inner ℝ v ω.1‖ ≤ M * ‖v‖ := by
    intro ω
    have hω : ‖ω.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ω.2
    have hy : x + r • ω.1 ∈ Metric.closedBall x r := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr, hω]
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |f (x + r • ω.1)| * ‖inner ℝ v ω.1‖ ≤ M * (‖v‖ * ‖ω.1‖) :=
        mul_le_mul (hM _ hy) (norm_inner_le_norm _ _) (norm_nonneg _) hMn
      _ = M * ‖v‖ := by rw [hω, mul_one]
  have hi := norm_integral_le_of_norm_le_const
    (μ := (volume.toSphere : Measure S)) (Filter.Eventually.of_forall hb)
  have hmass : (volume.toSphere : Measure S).real univ =
      (n : ℝ) * (volume : Measure E).real (Metric.ball 0 1) := by
    simp [S, E]
  have hvol : (volume : Measure E).real (Metric.ball x r) =
      r ^ n * (volume : Measure E).real (Metric.ball 0 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp [E, measureReal_def]
  have hu : (volume : Measure E).real (Metric.ball 0 1) ≠ 0 := by
    rw [measureReal_ne_zero_iff (measure_ball_lt_top.ne)]
    exact (Metric.measure_ball_pos volume (0 : E) zero_lt_one).ne'
  have hpow : r ^ n = r * r ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [pow_succ, mul_comm]
  rw [setAverage_eq, smul_eq_mul, abs_mul,
    MeasureTheory.integral_directional_derivative_ball hn hr hf v,
    abs_mul, abs_of_nonneg (pow_nonneg hr.le _),
    abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
  have hi' : |∫ ω : S, f (x + r • ω.1) * inner ℝ v ω.1 ∂volume.toSphere| ≤
      M * ‖v‖ * ((volume.toSphere : Measure S).real univ) := by
    simpa only [Real.norm_eq_abs] using hi
  calc
    _ ≤ ((volume : Measure E).real (Metric.ball x r))⁻¹ *
        (r ^ (n - 1) * (M * ‖v‖ * ((volume.toSphere : Measure S).real univ))) := by
      gcongr
    _ = (n / r) * M * ‖v‖ := by
      rw [hmass, hvol, hpow]
      field_simp [hu, hr.ne']
      <;> ring
