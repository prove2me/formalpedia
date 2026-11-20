-- Prove2me | solution 1 for LevyStochCalc.lintegral_sq_eq_eLpNorm_sq_on_triple_prod
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:17:54.876352+00:00
-- url     : https://prove2.me/submissions/622db832-0f37-48c5-80e0-79534874feac

import Definitions.Def_LevyStochCalc_Basic_F001

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

theorem _root_.solution
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {η : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite η]
    (h : α × β × γ → ℝ) (hh : Measurable h) :
    ∫⁻ x, ∫⁻ y, ∫⁻ z, (‖h (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂ν ∂μ
      = MeasureTheory.eLpNorm h 2 (μ.prod (ν.prod η)) ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_mul]
  have hm : Measurable (fun w : α × β × γ => (‖h w‖₊ : ℝ≥0∞) ^ 2) :=
    (hh.nnnorm.coe_nnreal_ennreal).pow_const 2
  simp only [ENNReal.toReal_ofNat]
  norm_num
  simp only [enorm_eq_nnnorm]
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hx : Measurable (fun w : β × γ => (‖h (x, w)‖₊ : ℝ≥0∞) ^ 2) :=
    hm.comp measurable_prodMk_left
  rw [lintegral_prod _ hx.aemeasurable]

end LevyStochCalc
