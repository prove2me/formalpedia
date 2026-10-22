-- Prove2me | solution 1 for JHolomorphic.lintegral_enorm_comp_smul_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:04:54.118226+00:00
-- url     : https://prove2.me/submissions/f4b99653-1d09-4230-8db2-c1b6b284a6a7

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex



namespace JHolomorphic

open MeasureTheory Metric

theorem lintegral_enorm_comp_smul_add_le_aux {E : Type*} [NormedAddCommGroup E]
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 1 ≤ p) {F : ℂ → E}
    (hF : AEStronglyMeasurable F μ) {s : ℝ} (hs : 0 < s) (a : ℂ) (S : Set ℂ) :
    ∫⁻ w in S, ‖F (s • w + a)‖ₑ ∂μ ≤
      ENNReal.ofReal (s ^ (-2 / p)) * eLpNorm F (ENNReal.ofReal p) μ * μ S ^ (1 - 1 / p) := by
  set q := ENNReal.ofReal p with hq
  have hq1 : (1 : ENNReal) ≤ q := ENNReal.one_le_ofReal.2 hp
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : 0 < p := by linarith
  have hqr : q.toReal = p := ENNReal.toReal_ofReal hp0.le
  set φ : ℂ → ℂ := fun w => s • w + a with hφ
  have hφm : Measurable φ := (measurable_const_smul s).add_const a
  set c : ENNReal := ENNReal.ofReal |(s ^ Module.finrank ℝ ℂ)⁻¹| with hc
  have hmap : Measure.map φ μ = c • μ := by
    have h1 : φ = (fun w => w + a) ∘ (fun w : ℂ => s • w) := rfl
    rw [h1, ← Measure.map_map (measurable_add_const a) (measurable_const_smul s),
      Measure.map_addHaar_smul μ hs.ne', Measure.map_smul, map_add_right_eq_self]
  have hqmp : Measure.QuasiMeasurePreserving φ μ μ := by
    refine ⟨hφm, ?_⟩
    rw [hmap]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) c
  have hFφ : AEStronglyMeasurable (F ∘ φ) μ := hF.comp_quasiMeasurePreserving hqmp
  calc ∫⁻ w in S, ‖F (s • w + a)‖ₑ ∂μ = eLpNorm (F ∘ φ) 1 (μ.restrict S) := by
        rw [eLpNorm_one_eq_lintegral_enorm]; rfl
    _ ≤ eLpNorm (F ∘ φ) q (μ.restrict S) * (μ.restrict S) Set.univ ^
          (1 / (1 : ENNReal).toReal - 1 / q.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq1 hFφ.restrict
    _ ≤ eLpNorm (F ∘ φ) q μ * μ S ^ (1 - 1 / p) := by
        rw [Measure.restrict_apply_univ, hqr, ENNReal.toReal_one, div_one]
        exact mul_le_mul_left (eLpNorm_mono_measure _ Measure.restrict_le_self) _
    _ = ENNReal.ofReal (s ^ (-2 / p)) * eLpNorm F q μ * μ S ^ (1 - 1 / p) := by
        congr 1
        rw [← eLpNorm_map_measure (by rw [hmap]; exact hF.smul_measure c) hφm.aemeasurable,
          hmap, eLpNorm_smul_measure_of_ne_top hqt, smul_eq_mul]
        congr 1
        rw [hc, Complex.finrank_real_complex, one_div, ENNReal.toReal_inv, hqr,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (inv_nonneg.2 hp0.le)]
        congr 1
        rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hs.le,
          ← Real.rpow_mul hs.le]
        push_cast
        ring_nf

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric

theorem solution {E : Type*} [NormedAddCommGroup E]
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 1 ≤ p) {F : ℂ → E}
    (hF : AEStronglyMeasurable F μ) {s : ℝ} (hs : 0 < s) (a : ℂ) (S : Set ℂ) :
    ∫⁻ w in S, ‖F (s • w + a)‖ₑ ∂μ ≤
      ENNReal.ofReal (s ^ (-2 / p)) * eLpNorm F (ENNReal.ofReal p) μ * μ S ^ (1 - 1 / p) :=
  lintegral_enorm_comp_smul_add_le_aux μ hp hF hs a S
