-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_avram_restart_payoff_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T00:15:32.55705+00:00
-- url     : https://prove2.me/submissions/1b38ce81-1217-4b59-9fb1-8cbf9414c806

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_real_avram_stopped_reward
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Mathlib.Tactic.Linarith
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.PartialOrder

open AvramDividend.Classical MeasureTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem clock_set_congr (Z : ℝ≥0 → ℝ) (P Q : ℝ → Prop) (h : ∀ u : ℝ≥0, P (Z u) ↔ Q (Z u)) : {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, 0 < u ∧ ↑u = t ∧ P (Z u)} = {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, 0 < u ∧ ↑u = t ∧ Q (Z u)} := by
  ext t; simp [h]
theorem passage_clock_eq {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (x a : ℝ) : (fun ω => ↑(tauPlus (shifted X.X x) a ω)) = twoSidedExitUpTime X (a - x) ∧ (fun ω => ↑(tauMinus (shifted X.X x) 0 ω)) = twoSidedExitDownTime X (-x) := by
  constructor <;> funext ω
  · simp only [tauPlus, shifted, twoSidedExitUpTime]
    erw [clock_set_congr _ (fun y => a < x + y) (fun y => a - x < y) (fun u => by constructor <;> intro h <;> linarith)]
    have hClock := source_result81_positive_open_clock_eq_all_times (fun s => X.X s ω) (Ioi (a - x)) isOpen_Ioi (X.rightCont ω)
    simp only [mem_Ioi] at hClock
    convert hClock using 2
    rfl
  · simp only [tauMinus, shifted, twoSidedExitDownTime]
    erw [clock_set_congr _ (fun y => x + y < 0) (fun y => y < -x) (fun u => by constructor <;> intro h <;> linarith)]
    have hClock := source_result81_positive_open_clock_eq_all_times (fun s => X.X s ω) (Iio (-x)) isOpen_Iio (X.rightCont ω)
    simp only [mem_Iio] at hClock
    convert hClock using 2
    rfl
theorem shifted_increments_rightCont {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (ω : Ω) (t s : ℝ≥0) : ContinuousWithinAt (fun v => X.X (t + v) ω - X.X t ω) (Ici s) s := by
  have hm : MapsTo (fun v : ℝ≥0 => t + v) (Ici s) (Ici (t + s)) := by intro v hv; simpa [mem_Ici] using add_le_add_right hv t
  exact ((X.rightCont ω (t + s)).comp (continuous_const.add continuous_id).continuousWithinAt hm).sub continuous_const.continuousWithinAt
theorem e2N (u : WithTop ℝ≥0) : ENNReal.toNNReal ↑u = WithTop.untopD 0 u := by cases u <;> rfl
theorem cLT {u l : WithTop ℝ≥0} : ((↑u : ℝ≥0∞) < (↑l : ℝ≥0∞)) = (u < l) := by cases u <;> cases l <;> simp
theorem weight_bridge (q : ℝ) (d : ℝ≥0 → ℝ) (hd : ∀ t, d t = discountedAt q ↑t) {u l : WithTop ℝ≥0} : (if u < l then d (WithTop.untopD 0 u) else 0) = (if u < l then discountedAt q u else 0) := by
  by_cases h : u < l <;> simp [h]
  cases u with
  | top => exact absurd h (not_lt_of_ge le_top)
  | coe a => exact hd a
theorem low_bridge (q : ℝ) {u l : WithTop ℝ≥0} : (if ↑l < ↑u then discountedAt q ↑l else 0) = (if l < u then discountedAt q l else 0) := by cases u <;> cases l <;> simp [discountedAt]
theorem restart_bridge (q : ℝ) (d g : ℝ≥0 → ℝ) (hd : ∀ t, d t = discountedAt q ↑t) {u l : WithTop ℝ≥0} : (if u < l then d (WithTop.untopD 0 u) * g (WithTop.untopD 0 u) else 0) = (if u < l then WithTop.recTopCoe 0 (fun t => discountedAt q ↑t * g t) u else 0) := by
  by_cases h : u < l <;> simp [h]
  cases u with
  | top => exact absurd h (not_lt_of_ge le_top)
  | coe a => simp [hd, WithTop.untopD, WithTop.recTopCoe]
theorem result81_restart_core (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (q x a : ℝ) (hq : 0 ≤ q) : let L := tauMinus (shifted X.X x) 0; let U := tauPlus (shifted X.X x) a; let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0; let restart := fun ω => if U ω < L ω then WithTop.recTopCoe 0 (fun t => discountedAt q ↑t * discountedAt q (tauMinus (fun s (_ : Unit) => a + (X.X (t + s) ω - X.X t ω)) 0 ())) (U ω) else 0; Integrable low P ∧ Integrable restart P ∧ (∫ ω, restart ω ∂P) = upBeforeDownExpectation P X.X q x a * downExpectation P X.X q a := by
  intro L U low restart
  have hU : (fun ω => ↑(U ω)) = twoSidedExitUpTime X (a - x) := by simpa [U] using (passage_clock_eq X x a).1
  have hL : (fun ω => ↑(L ω)) = twoSidedExitDownTime X (-x) := by simpa [L] using (passage_clock_eq X x a).2
  have hcond (ω) : (twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω) = (U ω < L ω) := by rw [← hU, ← hL]; exact cLT
  have hUom (ω) : (twoSidedExitUpTime X (a - x) ω).toNNReal = WithTop.untopD 0 (U ω) := by rw [← hU]; exact e2N _
  obtain ⟨hd, hb, reward, hm, he⟩ := source_result81_measurable_ruin_path_reward q a hq
  let d (t : ℝ≥0) := Real.exp (-q * (t : ℝ))
  let r (f : ℝ≥0 → ℝ) := min (max (reward f) 0) 1
  have hd_eq (t) : d t = discountedAt q ↑t := rfl
  have hdb : ∀ t, 0 ≤ d t ∧ d t ≤ 1 := fun t => ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (t.2))⟩
  have hr (f : ℝ≥0 → ℝ) (hf : ∀ t, ContinuousWithinAt f (Ici t) t) : r f = discountedAt q (tauMinus (fun s (_ : Unit) => a + f s) 0 ()) := by have hb' := hb (tauMinus (fun s (_ : Unit) => a + f s) 0 ()); dsimp [r]; rw [he f hf, max_eq_left hb'.1, min_eq_left hb'.2]
  have hfac := source_result81_uncapped_real_avram_stopped_reward X (-x) (a - x) d (by unfold d; fun_prop) hdb r ((hm.max measurable_const).min measurable_const) (fun f => ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩)
  clear_value d r
  have hdown (ω) : r (fun s => X.X s ω) = discountedAt q (tauMinus (shifted X.X a) 0 ω) := by simpa [shifted, tauMinus] using hr _ (X.rightCont ω)
  have hrestart (ω) : (if U ω < L ω then d (WithTop.untopD 0 (U ω)) * r (fun s => X.X (WithTop.untopD 0 (U ω) + s) ω - X.X (WithTop.untopD 0 (U ω)) ω) else 0) = restart ω := by simpa [restart, hr _ (shifted_increments_rightCont X ω (WithTop.untopD 0 (U ω)))] using restart_bridge q d (fun t => discountedAt q (tauMinus (fun s (_ : Unit) => a + (X.X (t + s) ω - X.X t ω)) 0 ())) hd_eq
  have hup (ω) : (if U ω < L ω then d (WithTop.untopD 0 (U ω)) else 0) = (if U ω < L ω then discountedAt q (U ω) else 0) := weight_bridge q d hd_eq
  have hUm : Measurable (fun ω => ↑(U ω)) := by rw [hU]; exact upperPassage_measurable_from_stopping X (a - x)
  have hLm : Measurable (fun ω => ↑(L ω)) := by rw [hL]; exact (avram_ws01h_lowerPassage_stopping_rightCont_filtration X (-x)).measurable_iSup.mono (iSup_le fun i => F.rightCont.le i) le_rfl
  have hlow : Integrable low P := by
    apply Integrable.congr _ (Eventually.of_forall fun ω => (low_bridge q).symm)
    have hboundUp : ∀ᵐ ω ∂P, ‖(if (↑(L ω) : ℝ≥0∞) < ↑(U ω) then discountedAt q (↑(L ω)) else 0)‖ ≤ 1 := by
      apply Eventually.of_forall
      intro ω
      split
      · have h1 := hb (↑(L ω)); rw [Real.norm_eq_abs, abs_of_nonneg h1.1]; exact h1.2
      · simp
    exact Integrable.of_bound (Measurable.ite (measurableSet_lt hLm hUm) (hd.comp hLm) measurable_const).aestronglyMeasurable 1 hboundUp
  have hInt : Integrable restart P := by
    convert hfac.1 using 1
    funext ω
    simp only [hcond ω, hUom ω]
    exact (hrestart ω).symm
  have hEq : (∫ ω, restart ω ∂P) = upBeforeDownExpectation P X.X q x a * downExpectation P X.X q a := by
    convert hfac.2 using 1
    · congr
      funext ω
      simp only [hcond ω, hUom ω]
      exact (hrestart ω).symm
    · congr
      · unfold upBeforeDownExpectation
        congr
        funext ω
        simp only [hcond ω, hUom ω]
        exact (hup ω).symm
      · unfold downExpectation
        congr
        funext ω
        exact (hdown ω).symm
  exact ⟨hlow, hInt, hEq⟩

theorem solution (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (q x a : ℝ) (hq : 0 ≤ q) : let L := tauMinus (shifted X.X x) 0; let U := tauPlus (shifted X.X x) a; let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0; let restart := fun ω => if U ω < L ω then WithTop.recTopCoe 0 (fun t => discountedAt q ↑t * discountedAt q (tauMinus (fun s (_ : Unit) => a + (X.X (t + s) ω - X.X t ω)) 0 ())) (U ω) else 0; Integrable low P ∧ Integrable restart P ∧ (∫ ω, restart ω ∂P) = upBeforeDownExpectation P X.X q x a * downExpectation P X.X q a := by
  exact result81_restart_core Ω P F X q x a hq
