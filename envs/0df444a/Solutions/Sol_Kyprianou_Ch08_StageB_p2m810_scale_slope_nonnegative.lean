-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_scale_slope_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:23:01.943803+00:00
-- url     : https://prove2.me/submissions/8037839f-297d-4cb1-926c-8fc3bc4253ac

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Verified reduction of record survival. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      0 < W q a ∧ 0 ≤ derivWithin (W q) (Ici a) a := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  have h8 := source_result8_2_v2
  unfold sourceCertificate_result8_2 at h8
  obtain ⟨n, hLaw, hRep, hder, _⟩ := h8 Ω P D ψ W hψ hW q hq
  obtain ⟨dl, dr, hl, hr, hdl, hdr, heq⟩ := hder a ha
  have hw := hRep.1 a ha
  refine ⟨hw, ?_⟩
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici a), hdr]
  exact mul_nonneg (add_nonneg ((hW q hq).1.2.1).1 ENNReal.toReal_nonneg) hw.le
