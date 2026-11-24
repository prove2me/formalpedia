-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_filtered_restart_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:27:36.215533+00:00
-- url     : https://prove2.me/submissions/3c34295c-05de-467c-8099-16adbe50465d

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_initial_controlled_ruin_clock
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_controlled_bad_clock
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_killed_discount
import Theorems.Thm_stageB_tauPlus_coe_eq
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
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
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q x a l : ℝ),
      0 ≤ q → 0 < a → 0 < x → x ≤ a → x < l →
      ∀ (ω : Ω),
      let U := twoSidedExitUpTime X x ω
      let L := twoSidedExitDownTime X (x-a) ω
      let u := U.toNNReal
      let c := l-x
      let reward := (let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
      let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
      let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)
      if U < R then discountedAt q U else 0)
      (if tauPlus X.X l ω < reflectedSupExit X.X x a ω
        then discountedAt q (tauPlus X.X l ω) else 0) =
      (if U < L then Real.exp (-q*(u:ℝ)) * reward else 0) := by
  intro Ω mΩ P hP F X q x a l hq ha hx hxa hl ω
  dsimp only
  let U := twoSidedExitUpTime X x ω
  let L := twoSidedExitDownTime X (x-a) ω
  let R := ruinTime X (a-x) (barrierStrategy X (a-x) a) ω
  have hR := p2m810_initial_controlled_ruin_clock Ω P F X x a ω hx.le hxa
  have hT := stageB_tauPlus_coe_eq X l ω
  have hsuccess : U < R ↔ U < L := by
    simpa [U,L,R,twoSidedExitUpTime,twoSidedExitDownTime] using
      barrierStrategy_upExit_before_controlledRuin_iff_rawExit X (a-x) a ha
        (sub_nonneg.mpr hxa) (by linarith) ω
  change (if (tauPlus X.X l ω : ℝ≥0∞) < (reflectedSupExit X.X x a ω : ℝ≥0∞)
    then discountedAt q (tauPlus X.X l ω) else 0) = _
  rw [hT,hR]
  by_cases hs : twoSidedExitUpTime X x ω < twoSidedExitDownTime X (x-a) ω
  · have hu : (U.toNNReal : ℝ≥0∞) = U := ENNReal.coe_toNNReal (ne_of_lt (hs.trans_le le_top))
    have hAt := firstUpcrossing_value_eq_threshold X x hx.le ω U.toNNReal hu
    have hUp := nextRecord_upclock_eq_add_shifted_inf X x (l-x) (sub_nonneg.mpr hl.le)
      U.toNNReal ω hu hAt
    have hDown := barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock X (a-x) a
      (by linarith) ω U.toNNReal (by simpa [U,twoSidedExitUpTime] using hu)
      (by rw [hu]; exact hsuccess.mpr hs)
    rw [p2m810_shifted_controlled_bad_clock Ω P F X a ω U.toNNReal] at hDown
    rw [show x+(l-x)=l by ring] at hUp
    let f : ℝ≥0 → ℝ := fun t => X.X (U.toNNReal+t) ω-X.X U.toNNReal ω
    let A : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // l-x < f t}, (i.1 : ℝ≥0∞)
    let B : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t-sSup (f '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞)
    have hUp' : twoSidedExitUpTime X l ω = (U.toNNReal : ℝ≥0∞) + A := by
      simpa only [A,f,iInf_subtype] using hUp
    have hDown' : ruinTime X (a-x) (barrierStrategy X (a-x) a) ω =
        (U.toNNReal : ℝ≥0∞) + B := hDown
    rw [hUp',hDown',if_pos hs]
    change (if (U.toNNReal : ℝ≥0∞) + A < (U.toNNReal : ℝ≥0∞) + B
      then discountedAt q ((U.toNNReal : ℝ≥0∞) + A) else 0) =
      Real.exp (-q*(U.toNNReal:ℝ)) * (if A < B then discountedAt q A else 0)
    exact p2m810_shifted_killed_discount q U.toNNReal A B
  · have hle : R ≤ U := le_of_not_gt (fun h => hs (hsuccess.mp h))
    have hmono := twoSidedExitUpTime_mono_threshold X x l hl.le ω
    have hn : ¬ twoSidedExitUpTime X l ω < R := not_lt_of_ge (hle.trans hmono)
    have hn' : ¬ twoSidedExitUpTime X l ω <
        ruinTime X (a-x) (barrierStrategy X (a-x) a) ω := hn
    change (if (twoSidedExitUpTime X l ω : ℝ≥0∞) < R
      then discountedAt q (twoSidedExitUpTime X l ω) else 0) =
      (if U < L then _ else 0)
    exact (if_neg hn).trans (if_neg (show ¬ U < L from hs)).symm
