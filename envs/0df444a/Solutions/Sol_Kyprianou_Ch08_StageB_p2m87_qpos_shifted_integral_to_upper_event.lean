-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_shifted_integral_to_upper_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:04:51.163453+00:00
-- url     : https://prove2.me/submissions/2ffae559-ef37-4810-9857-c472a93d80cb

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_positive_time_shift
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q a x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
      if U ω < L ω then disc t *
        (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
    (∫⁻ ω, ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue ∂P) =
    (∫⁻ ω, ∫⁻ t : ℝ≥0, disc t *
      (if U ω ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A
        then 1 else 0) ∂positiveTimeLebesgue ∂P)
:= by
  intro U L τ disc R
  obtain ⟨hU, hL⟩ := chat03_both_named_passage_clocks_measurable X (-x) (a - x)
  have hτ : Measurable τ := ENNReal.measurable_toNNReal.comp hU
  have hd : Measurable disc := by dsimp [disc]; fun_prop
  have hj := chat04_levy_joint_time_state_measurable X
  have ht : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp measurable_fst
  let B : Set (ℝ≥0 × Ω) := {z | (z.1 : ℝ≥0∞) < L z.2 ∧ x + X.X z.1 z.2 ∈ A}
  have hB : MeasurableSet B :=
    (measurableSet_lt ht (hL.comp measurable_snd)).inter ((measurable_const.add hj) hA)
  have hR : Measurable (Function.uncurry R) :=
    Measurable.ite (measurableSet_lt (hU.comp measurable_snd) (hL.comp measurable_snd))
      ((hd.comp measurable_fst).mul (Measurable.ite hB measurable_const measurable_const))
      measurable_const
  rw [p2m87_qpos_factor_positive_time_shift τ hτ R hR]
  refine lintegral_congr fun ω => lintegral_congr fun t => ?_
  by_cases h : U ω < L ω
  · have he : τ ω ≤ t ↔ U ω ≤ (t : ℝ≥0∞) := by
      have hc : (τ ω : ℝ≥0∞) = U ω := ENNReal.coe_toNNReal (ne_top_of_lt h)
      rw [← hc, ENNReal.coe_le_coe]
    by_cases hh : U ω ≤ (t : ℝ≥0∞) <;> simp [R, h, he, hh]
  · have hn : ¬ (U ω ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A) :=
      fun hh => h (lt_of_le_of_lt hh.1 hh.2.1)
    simp [R, h, hn]
