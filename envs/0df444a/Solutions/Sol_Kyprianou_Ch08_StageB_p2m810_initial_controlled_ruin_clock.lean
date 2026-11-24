-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_initial_controlled_ruin_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:16:35.411272+00:00
-- url     : https://prove2.me/submissions/65092c0f-143d-47d1-9b77-3a079f7127bd

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_initial_controlled_ruin_event
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact first-record clock reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (x a : ℝ) (ω : Ω), 0 ≤ x → x ≤ a →
      (reflectedSupExit X.X x a ω : ℝ≥0∞) =
        ruinTime X (a-x) (barrierStrategy X (a-x) a) ω := by
  intro Ω mΩ P F X x a ω hx hxa
  change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧ (u:ℝ≥0∞)=t ∧
    a < reflectAtSup X.X x u ω} = _
  unfold ruinTime
  apply le_antisymm
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    have hp : 0 < t := by
      by_contra! h
      have he : t = 0 := le_antisymm h bot_le
      rw [he] at ht
      simp [riskProcess,barrierStrategy,X.X_zero] at ht
      linarith
    exact sInf_le ⟨t,hp,rfl,(p2m810_initial_controlled_ruin_event
      Ω P F X x a ω t hx hxa hp).mpr ht⟩
  · apply le_sInf
    rintro _ ⟨t,ht,rfl,hcross⟩
    exact iInf₂_le t ((p2m810_initial_controlled_ruin_event
      Ω P F X x a ω t hx hxa ht).mp hcross)
