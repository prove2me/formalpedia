-- Prove2me | solution 1 for HunterPDE.Newtonian.tendsto_weighted_ball_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:54:32.806828+00:00
-- url     : https://prove2.me/submissions/fea2e577-29cf-4c14-b754-ad933b4e5612

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open HunterPDE.Newtonian

 theorem solution (n : ℕ) (hn : 2 ≤ n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun r : ℝ => fundamentalSolution n (r • v) *
      ∫ y in Metric.ball x r, g y) (𝓝[>] 0) (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => fundamentalSolution n (r • v) * r ^ n)
      (𝓝[>] 0) (𝓝 0) := by
    by_cases hn2 : n = 2
    · subst n
      have hl : Tendsto (fun r : ℝ => Real.log r * r) (𝓝[>] 0) (𝓝 0) := by
        simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
      have h := hl.mul (show Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds)
      have hh : Tendsto (fun r : ℝ => -(1 / (2 * Real.pi)) * (Real.log r * r) * r)
          (𝓝[>] 0) (𝓝 0) := by
        simpa only [mul_zero, zero_mul, mul_assoc] using h.const_mul (-(1 / (2 * Real.pi)))
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_Ioi] at hr
      simp [fundamentalSolution, norm_smul, hv, Real.norm_eq_abs, abs_of_pos hr, pow_two]
      ring
    · have h : Tendsto (fun r : ℝ =>
          (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n)) * r ^ 2)
          (𝓝[>] 0) (𝓝 0) := by
        simpa using ((show Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) from
          tendsto_id.mono_left nhdsWithin_le_nhds).pow 2).const_mul
          (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n))
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_Ioi] at hr
      simp only [fundamentalSolution, if_neg hn2, norm_smul, Real.norm_eq_abs,
        hv, mul_one, abs_of_pos hr]
      have he : r ^ n = r ^ (n - 2) * r ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      rw [he]
      field_simp [ne_of_gt hr]
  have hb : Tendsto (fun r : ℝ => ‖fundamentalSolution n (r • v) * r ^ n‖ *
      (C * unitBallVolume n)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hpow.norm.mul_const (C * unitBallVolume n)
  apply squeeze_zero_norm' _ hb
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [mem_Ioi] at hr
  have hi : ‖∫ y in Metric.ball x r, g y‖ ≤ C * volume.real (Metric.ball x r) :=
    norm_setIntegral_le_of_norm_le_const_ae (measure_ball_lt_top) (ae_of_all _ hC)
  have hm : volume.real (Metric.ball x r) = r ^ n * unitBallVolume n := by
    rw [measureReal_def, addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul]
    simp [ENNReal.toReal_ofReal (pow_nonneg hr.le _), unitBallVolume]
  rw [norm_mul]
  calc
    ‖fundamentalSolution n (r • v)‖ * ‖∫ y in Metric.ball x r, g y‖ ≤
        ‖fundamentalSolution n (r • v)‖ * (C * volume.real (Metric.ball x r)) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = ‖fundamentalSolution n (r • v) * r ^ n‖ * (C * unitBallVolume n) := by
      rw [hm, norm_mul, Real.norm_of_nonneg (pow_nonneg hr.le _)]
      ring

