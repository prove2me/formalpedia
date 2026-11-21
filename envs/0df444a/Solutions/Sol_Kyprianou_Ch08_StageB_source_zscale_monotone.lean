-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_zscale_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:46:18.539872+00:00
-- url     : https://prove2.me/submissions/1c19469e-42f2-4e2d-b809-3deaf8b95a94

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x y : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Zscale q (W q) x ≤ Zscale q (W q) y := by
  rcases source_family_positive_monotone ψ W hW q hq with
    ⟨hpos, _, hcont⟩
  have hy : 0 ≤ y := hx.trans hxy
  have hIcc : ContinuousOn (W q) (Set.Icc (0 : ℝ) y) :=
    hcont.mono (by intro z hz; exact hz.1)
  have hi : IntervalIntegrable (W q) volume 0 y := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mp
      hIcc.integrableOn_Icc
  have hint : (∫ z in (0 : ℝ)..x, W q z) ≤
      (∫ z in (0 : ℝ)..y, W q z) := by
    apply intervalIntegral.integral_mono_interval le_rfl hx hxy
    · filter_upwards [] with z
      exact hpos z
    · exact hi
  dsimp [Zscale]
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hint)]
