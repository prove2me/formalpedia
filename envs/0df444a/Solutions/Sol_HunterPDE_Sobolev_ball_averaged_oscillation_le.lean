-- Prove2me | solution 1 for HunterPDE.Sobolev.ball_averaged_oscillation_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T07:01:46.914332+00:00
-- url     : https://prove2.me/submissions/85324619-e05d-4ff8-9fac-aece44ee28cf

import Theorems.Thm_HunterPDE_Sobolev_centered_ball_oscillation_le_potential
import Theorems.Thm_MeasureTheory_lintegral_mul_rieszKernel_ball_le
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory MeasureTheory.Measure

theorem solution {n : ℕ} {p : ℝ}
    (hn : 0 < n) (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ∀ (a : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ∀ x ∈ Metric.ball a r,
        (∫⁻ z in Metric.ball a r, ENNReal.ofReal |f x - f z|) ≤
          volume (Metric.ball a r) * (C : ENNReal) *
            eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball a (3 * r))) *
            ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
  obtain ⟨A, hA⟩ := HunterPDE.Sobolev.centered_ball_oscillation_le_potential hn
  obtain ⟨D, hD⟩ := MeasureTheory.lintegral_mul_rieszKernel_ball_le hn hnp
  refine ⟨2 ^ n * A * D * 2, fun f hf a r hr x hx => ?_⟩
  have hr2 : 0 < 2 * r := by linarith
  have hsub : Metric.ball a r ⊆ Metric.ball x (2 * r) := by
    intro z hz
    change dist z x < 2 * r
    calc
      dist z x ≤ dist z a + dist a x := dist_triangle _ _ _
      _ < r + r := add_lt_add hz (by simpa [dist_comm] using hx)
      _ = _ := by ring
  have hsub3 : Metric.ball x (2 * r) ⊆ Metric.ball a (3 * r) := by
    intro z hz
    change dist z a < 3 * r
    calc
      dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
      _ < 2 * r + r := add_lt_add hz hx
      _ = _ := by ring
  have hgm : AEStronglyMeasurable (fun z => ‖gradient f z‖) volume := by
    have hc := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))
    exact hc.norm.aestronglyMeasurable
  have hpot := hD (fun z => ‖gradient f z‖) hgm x (2 * r) hr2
  simp only [abs_norm] at hpot
  have hG : eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x (2 * r))) ≤
      eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball a (3 * r))) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hsub3 le_rfl)
  have hvol : volume (Metric.ball x (2 * r)) =
      (2 : ENNReal) ^ n * volume (Metric.ball a r) := by
    rw [addHaar_ball_of_pos volume x hr2, addHaar_ball_of_pos volume a hr]
    simp only [finrank_euclideanSpace, Fintype.card_fin, mul_pow,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n), ENNReal.ofReal_pow
        (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    ring
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hα : 1 - (n : ℝ) / p ≤ 1 :=
    sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hp.le)
  have hscale : ENNReal.ofReal ((2 * r) ^ (1 - (n : ℝ) / p)) ≤
      2 * ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
    have h : (2 * r) ^ (1 - (n : ℝ) / p) ≤ 2 * r ^ (1 - (n : ℝ) / p) := by
      rw [Real.mul_rpow (by norm_num) hr.le]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h
  calc
    _ ≤ ∫⁻ z in Metric.ball x (2 * r), ENNReal.ofReal |f x - f z| :=
      lintegral_mono_set hsub
    _ ≤ volume (Metric.ball x (2 * r)) * (A : ENNReal) *
        (∫⁻ z in Metric.ball x (2 * r), ENNReal.ofReal ‖gradient f z‖ *
          ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := hA f hf x (2 * r) hr2
    _ ≤ volume (Metric.ball x (2 * r)) * (A : ENNReal) *
        ((D : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x (2 * r))) *
            ENNReal.ofReal ((2 * r) ^ (1 - (n : ℝ) / p))) :=
      by simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_left hpot (volume (Metric.ball x (2 * r)) * (A : ENNReal))
    _ ≤ volume (Metric.ball x (2 * r)) * (A : ENNReal) *
        ((D : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball a (3 * r)))) *
            (2 * ENNReal.ofReal (r ^ (1 - (n : ℝ) / p))) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul'
        (mul_le_mul_left (mul_le_mul_left hG (D : ENNReal))
          (volume (Metric.ball x (2 * r)) * (A : ENNReal))) hscale
    _ = _ := by
      rw [hvol]
      simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
      ring
