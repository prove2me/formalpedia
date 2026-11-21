-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_technicalFullMomentExponentExistence_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:08:33.256476+00:00
-- url     : https://prove2.me/submissions/2f759105-61f1-4ccc-91d9-c835feef5d19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_moment_log_scaling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution : technicalFullMomentExponentExistence := by
  intro Ω _ P _ D
  let ψ : ℝ → ℝ := fun β => Real.log (∫ ω, Real.exp (β * D.X 1 ω) ∂P)
  refine ⟨ψ, ?_, ?_⟩
  · intro β t hβ ht
    have hm := (source_result81_law_positive_mgf Ω P D t β hβ).1
    exact ⟨hm, (source_result81_finite_moment_log_scaling Ω P D t ht β hm).2⟩
  · intro c t ht hm
    exact source_result81_finite_moment_log_scaling Ω P D t ht c hm
