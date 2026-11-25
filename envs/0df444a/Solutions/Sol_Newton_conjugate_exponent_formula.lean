-- Prove2me | solution 1 for Newton.conjugate_exponent_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:39.662436+00:00
-- url     : https://prove2.me/submissions/8f23868b-ffc8-445a-baa8-3e2d33728450

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞)
    (hp : 1 < p) (hp_top : p < ∞) :
    ∃ q : ℝ≥0∞, IsConjugateExponent p q ∧
    q = ENNReal.ofReal (p.toReal / (p.toReal - 1)) := by
  have hp_ne_top : p ≠ ∞ := ne_of_lt hp_top
  set pr := p.toReal with hpr
  have hpr_gt_one : 1 < pr := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp_ne_top).2 hp
    simpa [hpr] using this
  have hpr_pos : 0 < pr := zero_lt_one.trans hpr_gt_one
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hpr_sub_pos : 0 < pr - 1 := sub_pos.2 hpr_gt_one
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := ne_of_gt hpr_sub_pos
  set qrReal := pr / (pr - 1) with hqrReal
  set q : ℝ≥0∞ := ENNReal.ofReal qrReal with hq
  have hq_ne_top : q ≠ ∞ := by simp [hq]
  have hq_pos_real : 0 < qrReal := div_pos hpr_pos hpr_sub_pos
  have hq_real_gt_one : 1 < qrReal := by
    have hdiff : qrReal - 1 = 1 / (pr - 1) := by
      rw [hqrReal]
      field_simp
      ring
    have hpos' : 0 < qrReal - 1 := by
      have h := one_div_pos.2 hpr_sub_pos
      exact hdiff.symm ▸ h
    exact sub_pos.mp hpos'
  have hq_gt_one : 1 < q := by
    have h := (ENNReal.ofReal_lt_ofReal_iff hq_pos_real).2 hq_real_gt_one
    simpa [hq] using h
  have hq_lt_top : q < ∞ := by simp [hq]
  have hp_ofReal : ENNReal.ofReal pr = p := by
    simp [hp_ne_top, hpr]
  have hp_inv : p⁻¹ = ENNReal.ofReal (1 / pr) := by
    have := (ENNReal.ofReal_inv_of_pos hpr_pos).symm
    simpa [hp_ofReal, one_div] using this
  have hq_inv : q⁻¹ = ENNReal.ofReal (1 / qrReal) := by
    have := (ENNReal.ofReal_inv_of_pos hq_pos_real).symm
    simpa [hq, one_div] using this
  have hsum_real : 1 / pr + 1 / qrReal = 1 := by
    rw [hqrReal]
    field_simp
    ring
  have hsum_real_inv : pr⁻¹ + qrReal⁻¹ = 1 := by simpa [one_div] using hsum_real
  have hsum : 1 / p + 1 / q = 1 := by
    have h1 : 0 ≤ 1 / pr := by positivity
    have h2 : 0 ≤ 1 / qrReal := by positivity
    calc
      1 / p + 1 / q = p⁻¹ + q⁻¹ := by simp [one_div]
      _ = ENNReal.ofReal (1 / pr) + ENNReal.ofReal (1 / qrReal) := by simp [hp_inv, hq_inv]
      _ = ENNReal.ofReal (1 / pr + 1 / qrReal) := (ENNReal.ofReal_add h1 h2).symm
      _ = ENNReal.ofReal 1 := by simp [hsum_real_inv]
      _ = 1 := by simp
  refine ⟨q, ?_, by simp [hq, hpr, hqrReal]⟩
  refine Or.inr ?_
  refine Or.inr ?_
  exact ⟨hp, hp_top, hq_gt_one, hq_lt_top, hsum⟩
end Newton
