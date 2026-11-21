-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_scale_exists_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:31:58.885799+00:00
-- url     : https://prove2.me/submissions/87920d6f-ecda-4bee-8e52-46f59f0f88c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_normalized_scale_at_discount
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ W : ℝ → ℝ → ℝ, HasSourceScaleFamily ψ W ∧
      ∀ q a : ℝ, 0 ≤ q → 0 < a → 0 < W q a := by
  classical
  have hex (q : ℝ) : 0 ≤ q → ∃ w : ℝ → ℝ, IsQScale ψ q w :=
    source_result81_normalized_scale_at_discount Ω P D ψ hψ q
  let W (q : ℝ) : ℝ → ℝ := if hq : 0 ≤ q then Classical.choose (hex q hq) else 0
  have hW : HasSourceScaleFamily ψ W := by
    intro q hq
    simpa only [W, dif_pos hq] using Classical.choose_spec (hex q hq)
  obtain ⟨K, hK, hbound⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
  exact ⟨W, hW, fun q a hq ha =>
    source_result81_scale_positive_from_quadratic ψ q (W q) (hW q hq) K hK hbound a ha⟩
