-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_record_restart_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:06:21.454022+00:00
-- url     : https://prove2.me/submissions/a7a4412a-d7d4-4e87-affc-81c8cd6baf6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_restart_factor
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source record regeneration. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a l : ℝ), 0 ≤ q → 0 < a → 0 < x → x ≤ a → x < l →
      (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
        then discountedAt q (tauPlus D.X l ω) else 0 ∂P) =
      upBeforeDownExpectation P D.X q (a-x) a *
      (∫ ω, if tauPlus D.X (l-x) ω < reflectedSupExit D.X 0 a ω
        then discountedAt q (tauPlus D.X (l-x) ω) else 0 ∂P) := by
  intro Ω mΩ P hP D ψ W hψ hW q x a l hq ha hx hxa hl
  obtain ⟨F,X,hX,_⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have h := p2m810_filtered_restart_factor Ω P F X q x a l hq ha hx hxa hl
  have he (y b : ℝ) : (∫ ω, if tauPlus X.X b ω < reflectedSupExit X.X y a ω
        then discountedAt q (tauPlus X.X b ω) else 0 ∂P) =
      (∫ ω, if tauPlus D.X b ω < reflectedSupExit D.X y a ω
        then discountedAt q (tauPlus D.X b ω) else 0 ∂P) := by
    apply integral_congr_ae
    filter_upwards [hX] with ω hw
    simp only [tauPlus,reflectedSupExit,reflectAtSup,Kyprianou.Ch08.runningSup,hw]
    congr
  have hu : upBeforeDownExpectation P X.X q (a-x) a =
      upBeforeDownExpectation P D.X q (a-x) a := by
    unfold upBeforeDownExpectation
    apply integral_congr_ae
    filter_upwards [hX] with ω hw
    simp only [tauPlus,tauMinus,shifted,hw]
    congr
  rwa [he x l,hu,he 0 (l-x)] at h
