-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_filtered_fresh_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:20:57.527175+00:00
-- url     : https://prove2.me/submissions/ae424fd4-fcd5-404c-b7c1-658c6c0e4b1c

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_origin_drawdown_clock
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The origin clocks agree on the actual path. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q a c : ℝ),
      0 < a → 0 < c →
      ∀ (ω : Ω),
      let u : ℝ≥0 := 0
      (let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
      let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
      let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)
      if U < R then discountedAt q U else 0) =
      (if tauPlus X.X c ω < reflectedSupExit X.X 0 a ω
        then discountedAt q (tauPlus X.X c ω) else 0) := by
  intro Ω mΩ P hP F X q a c ha hc ω
  let G (f : ℝ≥0 → ℝ) : ℝ :=
    let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
    let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞)
    if U < R then discountedAt q U else 0
  change G (fun t => X.X (0+t) ω-X.X 0 ω) = _
  have hf : (fun t : ℝ≥0 => X.X (0+t) ω-X.X 0 ω) = fun t => X.X t ω := by
    funext t
    simp [X.X_zero]
  rw [hf]
  have hU : (tauPlus X.X c ω : ℝ≥0∞) =
      ⨅ i : {t : ℝ≥0 // c < X.X t ω}, (i.1 : ℝ≥0∞) := by
    change sInf {t : ℝ≥0∞ | ∃ u : ℝ≥0, 0 < u ∧
      (u:ℝ≥0∞) = t ∧ c < X.X u ω} = _
    simpa only [mem_Ioi,iInf_subtype] using
      source_result81_positive_open_clock_eq_all_times
        (fun t => X.X t ω) (Ioi c) isOpen_Ioi (X.rightCont ω)
  have hR := p2m810_origin_drawdown_clock Ω P F X a ω ha
  have hp : ((tauPlus X.X c ω : ℝ≥0∞),
      (reflectedSupExit X.X 0 a ω : ℝ≥0∞)) =
      ((⨅ i : {t : ℝ≥0 // c < X.X t ω}, (i.1 : ℝ≥0∞)),
        (⨅ i : {t : ℝ≥0 // X.X t ω -
          sSup ((fun r => X.X r ω) '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞))) :=
    Prod.ext hU hR
  exact congrArg (fun p : ℝ≥0∞ × ℝ≥0∞ =>
    if p.1 < p.2 then discountedAt q p.1 else 0) hp.symm
