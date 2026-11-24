-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_avram_clock_section_to_strict_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:08:29.503945+00:00
-- url     : https://prove2.me/submissions/03911619-6302-4d83-8322-4f65754abac4

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_source_lower_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_product_sections
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact source clock reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q x : ℝ, 0 < q → 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
      let f : ℝ≥0 → ℝ≥0∞ := fun t =>
        P {ω | (t : WithTop ℝ≥0) <
          tauMinus (shifted X.X x) 0 ω ∧ shifted X.X x t ω ∈ A}
      Measurable f ∧
        (∫⁻ r : ℝ, f r.toNNReal ∂expMeasure q) =
        (P.prod (expMeasure q)) {z : Ω × ℝ | 0 ≤ z.2 ∧
          ENNReal.ofReal z.2 < AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
          x + X.X z.2.toNNReal z.1 ∈ A} := by
  intro Ω mΩ P hP F X q x hq hx A hA
  dsimp only
  let B : Set (Ω × ℝ≥0) := {z | (z.2 : ℝ≥0∞) <
    AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
    x + X.X z.2 z.1 ∈ A}
  have hτ := (AvramDividend.Classical.chat03_both_named_passage_clocks_measurable
    X (-x) 0).2
  have hT : Measurable (fun z : Ω × ℝ≥0 => x + X.X z.2 z.1) :=
    measurable_const.add
      ((AvramDividend.Classical.chat04_levy_joint_time_state_measurable X).comp
        (measurable_snd.prodMk measurable_fst))
  have hB : MeasurableSet B :=
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_snd)
      (hτ.comp measurable_fst)).inter (hT hA)
  have hs := p2m88_exp_clock_product_sections Ω P q hq B hB
  have hsection : (fun t : ℝ≥0 =>
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted X.X x) 0 ω ∧
        shifted X.X x t ω ∈ A}) = fun t => P ((fun ω : Ω => (ω, t)) ⁻¹' B) := by
    funext t
    congr 1
    ext ω
    change ((t : ℝ≥0∞) < (tauMinus (shifted X.X x) 0 ω : ℝ≥0∞) ∧
        x + X.X t ω ∈ A) ↔
      ((t : ℝ≥0∞) < AvramDividend.Classical.twoSidedExitDownTime X (-x) ω ∧
        x + X.X t ω ∈ A)
    rw [p2m88_avram_source_lower_clock_eq Ω P F X x ω]
  constructor
  · rw [hsection]
    exact hs.1
  · calc
      _ = ∫⁻ r : ℝ, P ((fun ω : Ω => (ω, r.toNNReal)) ⁻¹' B) ∂expMeasure q :=
        lintegral_congr (fun r => congrFun hsection r.toNNReal)
      _ = _ := hs.2
