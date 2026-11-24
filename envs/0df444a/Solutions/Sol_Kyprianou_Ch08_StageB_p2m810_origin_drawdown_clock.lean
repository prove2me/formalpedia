-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_origin_drawdown_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:18:53.760461+00:00
-- url     : https://prove2.me/submissions/8c1b7961-bbe3-419a-b2ba-f95bd571c87d

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_origin_drawdown_event
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Origin drawdown crossing set identification. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (a : ℝ) (ω : Ω), 0 < a →
      (reflectedSupExit X.X 0 a ω : ℝ≥0∞) =
      ⨅ i : {t : ℝ≥0 // X.X t ω -
        sSup ((fun t => X.X t ω) '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞) := by
  intro Ω mΩ P F X a ω ha
  let f : ℝ≥0 → ℝ := fun t => X.X t ω
  have he (t : ℝ≥0) : a < reflectAtSup X.X 0 t ω ↔
      f t - sSup (f '' Icc 0 t) < -a :=
    p2m810_origin_drawdown_event Ω P F X a ω t
  have hpos (t : ℝ≥0) (h : f t - sSup (f '' Icc 0 t) < -a) : 0 < t := by
    by_contra! hn
    have ht : t = 0 := le_antisymm hn bot_le
    subst t
    simp [f,X.X_zero] at h
    linarith
  have hR : (reflectedSupExit X.X 0 a ω : ℝ≥0∞) =
      ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞) := by
    unfold reflectedSupExit tauPlus
    apply le_antisymm
    · apply le_iInf
      intro i
      exact sInf_le ⟨i.1,hpos i.1 i.2,rfl,(he i.1).mpr i.2⟩
    · apply le_sInf
      rintro _ ⟨t,ht,rfl,hh⟩
      exact iInf_le (fun i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a} =>
        (i.1 : ℝ≥0∞)) ⟨t,(he t).mp hh⟩
  exact hR
