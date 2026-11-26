-- Prove2me | solution 1 for Kyprianou.Ch04.bvExponentSlopeLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:14:40.138353+00:00
-- url     : https://prove2.me/submissions/a263f7df-5a3d-4a10-91a3-d7af8fd074bf

import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    Tendsto (fun beta : ℝ => L.ψ beta / beta)
      atTop (nhds L.drift) := by
  have h := AvramDividend.Classical.bv_exponent_gap_div_tendsto_zero L hBV
  have hl : Tendsto
      (fun beta : ℝ => L.drift - (L.drift * beta - L.ψ beta) / beta)
      atTop (nhds L.drift) := by
    simpa using (tendsto_const_nhds.sub h)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hb
  field_simp [hb.ne'] <;> ring
