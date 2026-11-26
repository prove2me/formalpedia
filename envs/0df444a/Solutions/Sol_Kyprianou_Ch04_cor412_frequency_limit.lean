-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_frequency_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:31:30.998795+00:00
-- url     : https://prove2.me/submissions/77ceadea-5b98-4b21-a248-a33557a56acd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (m : ℝ) :
    Tendsto (fun b : ℝ => m * b / L.ψ b) atTop (𝓝 (m / L.drift)) := by
  have hg := bv_exponent_gap_div_tendsto_zero L hBV
  have hq : Tendsto (fun b : ℝ => L.ψ b / b) atTop (𝓝 L.drift) := by
    have h := (tendsto_const_nhds.sub hg :
      Tendsto (fun b : ℝ => L.drift - (L.drift * b - L.ψ b) / b)
        atTop (𝓝 (L.drift - 0)))
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    field_simp [hb.ne']
    <;> ring
  have h := (tendsto_const_nhds.div hq hd.ne' :
    Tendsto (fun b : ℝ => m / (L.ψ b / b)) atTop (𝓝 (m / L.drift)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  change m / (L.ψ b / b) = m * b / L.ψ b
  rw [div_div_eq_mul_div]
