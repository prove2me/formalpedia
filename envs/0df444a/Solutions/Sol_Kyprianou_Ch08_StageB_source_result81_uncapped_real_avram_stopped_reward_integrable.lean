-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:24:28.854303+00:00
-- url     : https://prove2.me/submissions/28cb70b9-f765-45c3-a77f-5210eeecc165

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weight := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoff := fun ω => if U ω < L ω then discount (U ω).toNNReal * reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω) else 0
    Integrable payoff P ∧ Integrable weight P ∧ Integrable (fun ω => reward (fun s => X.X s ω)) P := by
  classical
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X upper
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X lower
  let τU : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
  let shiftPath : Ω → (ℝ≥0 → ℝ) := fun ω s => X.X (τU ω + s) ω - X.X (τU ω) ω
  let origPath : Ω → (ℝ≥0 → ℝ) := fun ω s => X.X s ω
  let weightR : Ω → ℝ := fun ω => if U ω < L ω then discount (τU ω) else 0
  let payoffR : Ω → ℝ := fun ω => if U ω < L ω then discount (τU ω) * reward (shiftPath ω) else 0
  let origR : Ω → ℝ := fun ω => reward (origPath ω)
  obtain ⟨hU, -⟩ := chat03_both_named_passage_clocks_measurable X lower upper
  have hEvt : MeasurableSet {ω : Ω | U ω < L ω} := chat03_upper_before_lower_passage_event_measurable X lower upper
  have hτU : Measurable τU := hU.ennreal_toNNReal
  have hShift : Measurable shiftPath := avram_ws01e_b_randomAge_whole_shiftedPath_measurable X τU hτU
  have hOrigPath : Measurable origPath := measurable_pi_lambda _ (fun s => (chat04_levy_joint_time_state_measurable X).comp (measurable_const.prodMk measurable_id))
  have hPayMeas : Measurable payoffR := Measurable.ite hEvt ((hd.comp hτU).mul (hr.comp hShift)) measurable_const
  have hWMeas : Measurable weightR := Measurable.ite hEvt (hd.comp hτU) measurable_const
  have hOMeas : Measurable origR := hr.comp hOrigPath
  have hPayNN : ∀ ω, 0 ≤ payoffR ω := fun ω => by simp only [payoffR]; split_ifs with h; exacts [mul_nonneg (hdb _).1 (hrb _).1, le_rfl]
  have hPayLe1 : ∀ ω, payoffR ω ≤ 1 := fun ω => by
    simp only [payoffR]
    split_ifs with h
    · nlinarith [(hdb (τU ω)).1, (hdb (τU ω)).2, (hrb (shiftPath ω)).1, (hrb (shiftPath ω)).2]
    · exact zero_le_one
  have hWNN : ∀ ω, 0 ≤ weightR ω := fun ω => by simp only [weightR]; split_ifs with h; exacts [(hdb _).1, le_rfl]
  have hWLe1 : ∀ ω, weightR ω ≤ 1 := fun ω => by simp only [weightR]; split_ifs with h; exacts [(hdb _).2, zero_le_one]
  have hONN : ∀ ω, 0 ≤ origR ω := fun ω => (hrb _).1
  have hOLe1 : ∀ ω, origR ω ≤ 1 := fun ω => (hrb _).2
  have hPayInt : Integrable payoffR P := Integrable.of_bound hPayMeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hPayNN ω)]; exact hPayLe1 ω)
  have hWInt : Integrable weightR P := Integrable.of_bound hWMeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hWNN ω)]; exact hWLe1 ω)
  have hOInt : Integrable origR P := Integrable.of_bound hOMeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hONN ω)]; exact hOLe1 ω)
  exact ⟨hPayInt, hWInt, hOInt⟩
