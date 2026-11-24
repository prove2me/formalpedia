-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_record_survival_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:09:19.818116+00:00
-- url     : https://prove2.me/submissions/1697d703-b32b-4f97-9090-6deeabf097db

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_strict_record_origin
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_restart_factor
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_scale_slope_nonnegative
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Regenerate at the initial record, then use strict survival from zero. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ l : ℝ, x < l →
        (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) =
        W q (a-x) / W q a *
          Real.exp (-(derivWithin (W q) (Ici a) a / W q a) * (l-x)) := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa l hl
  rcases eq_or_lt_of_le hx with he | hp
  · subst x
    have hw := (p2m810_scale_slope_nonnegative Ω P D ψ W hψ hW q 0 a hq ha le_rfl ha.le).1
    simpa [hw.ne'] using p2m810_strict_record_origin Ω P D ψ W hψ hW q a l hq ha hl
  · rw [p2m810_record_restart_factor Ω P D ψ W hψ hW q x a l hq ha hp hxa hl]
    rw [source_result81_upper_exit_ratio Ω P D ψ hψ W hW q (a-x) a hq ha (by linarith)]
    rw [p2m810_strict_record_origin Ω P D ψ W hψ hW q a (l-x) hq ha (sub_pos.mpr hl)]
