-- Prove2me | solution 1 for HunterPDE.Sobolev.morrey_increment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T22:02:58.784852+00:00
-- url     : https://prove2.me/submissions/a5768e87-8998-48d9-8ca5-6d6326b4f226

import Theorems.Thm_HunterPDE_Sobolev_ball_averaged_oscillation_le
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith

open MeasureTheory

theorem solution {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p) :
    ∃ A : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ x y, ENNReal.ofReal |f x - f y| ≤
        (A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume *
          ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ) / p)) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0, fun f _ _ x y => ?_⟩
    have hxy : x = y := Subsingleton.elim _ _
    simp [hxy]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨C, hC⟩ := HunterPDE.Sobolev.ball_averaged_oscillation_le hnpos hnp
  refine ⟨4 * C, fun f hf _ x y => ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  let d : ℝ := ‖x - y‖
  let α : ℝ := 1 - (n : ℝ) / p
  let G : ENNReal := eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume
  let B := Metric.ball x (2 * d)
  let v : ENNReal := volume B
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hr : 0 < 2 * d := by positivity
  have hxB : x ∈ B := by simpa [B] using hr
  have hyB : y ∈ B := by
    change dist y x < 2 * d
    rw [dist_comm, dist_eq_norm]
    change d < 2 * d
    linarith
  have hv0 : v ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hvt : v ≠ ⊤ := measure_ball_lt_top.ne
  have hG : eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x (3 * (2 * d)))) ≤ G :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hbound (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ B) :
      (∫⁻ z in B, ENNReal.ofReal |f w - f z|) ≤
        v * (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) := by
    exact (hC f hf x (2 * d) hr w hw).trans
      (mul_le_mul_left (mul_le_mul_right hG _) _)
  have hmeas : Measurable (fun z => ENNReal.ofReal |f x - f z|) :=
    (continuous_const.sub hf.continuous).abs.measurable.ennreal_ofReal
  have htriangle : ENNReal.ofReal |f x - f y| * v ≤
      v * (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) +
        v * (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) := by
    calc
      _ = ∫⁻ _z in B, ENNReal.ofReal |f x - f y| := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in B, (ENNReal.ofReal |f x - f z| + ENNReal.ofReal |f y - f z|) := by
        apply lintegral_mono
        intro z
        calc
          _ ≤ ENNReal.ofReal (|f x - f z| + |f y - f z|) :=
            ENNReal.ofReal_le_ofReal (by simpa [abs_sub_comm] using abs_sub_le (f x) (f z) (f y))
          _ = _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ = (∫⁻ z in B, ENNReal.ofReal |f x - f z|) +
          (∫⁻ z in B, ENNReal.ofReal |f y - f z|) := lintegral_add_left hmeas _
      _ ≤ _ := add_le_add (hbound x hxB) (hbound y hyB)
  have hcancel : ENNReal.ofReal |f x - f y| ≤
      (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) +
        (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) := by
    apply (ENNReal.mul_le_mul_iff_left hv0 hvt).mp
    simpa only [add_mul, mul_assoc, mul_comm, mul_left_comm] using htriangle
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hnp
  have hα : α ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hp.le)
  have hscale : (2 * d) ^ α ≤ 2 * d ^ α := by
    rw [Real.mul_rpow (by norm_num) hd.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα
  have hscale' : ENNReal.ofReal ((2 * d) ^ α) ≤ 2 * ENNReal.ofReal (d ^ α) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hscale
  calc
    _ ≤ _ := hcancel
    _ ≤ (C : ENNReal) * G * (2 * ENNReal.ofReal (d ^ α)) +
          (C : ENNReal) * G * (2 * ENNReal.ofReal (d ^ α)) :=
      add_le_add (mul_le_mul_right hscale' _) (mul_le_mul_right hscale' _)
    _ = _ := by
      simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      ring
