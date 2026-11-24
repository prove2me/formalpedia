-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_avram_two_sided_occupation_sections_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T03:07:58.241237+00:00
-- url     : https://prove2.me/submissions/0f14bde3-b225-4de0-b0c1-c3cad1650f5c

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_upper_shifted_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_source_lower_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_product_sections
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
/-- Measurability of two-sided killed sections in the filtered Avram model. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ)
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ (A : Set ℝ), MeasurableSet A →
    Measurable (fun t : ℝ≥0 =>
      P {ω | (t : WithTop ℝ≥0) <
        min (tauMinus (shifted X.X x) 0 ω)
          (tauPlus (shifted X.X x) a ω) ∧
        shifted X.X x t ω ∈ A}) := by
  intro Ω mΩ P hP F X a x ha hx hxa A hA
  have hupper : ∀ ω : Ω,
      (tauPlus (shifted X.X x) a ω : ℝ≥0∞) =
        AvramDividend.Classical.twoSidedExitUpTime X (a - x) ω := by
    intro ω
    exact qzero_avram_upper_shifted_clock_eq Ω P F X a x ha hx hxa ω
  have hlower : ∀ ω : Ω,
      (tauMinus (shifted X.X x) 0 ω : ℝ≥0∞) =
        AvramDividend.Classical.twoSidedExitDownTime X (-x) ω := by
    intro ω
    exact p2m88_avram_source_lower_clock_eq Ω P F X x ω
  let B : Set (Ω × ℝ≥0) :=
    {z | (z.2 : ℝ≥0∞) <
        AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1 ∧
      (z.2 : ℝ≥0∞) <
        AvramDividend.Classical.twoSidedExitUpTime X (a - x) z.1 ∧
      x + X.X z.2 z.1 ∈ A}
  have hclocks :=
    (AvramDividend.Classical.chat03_both_named_passage_clocks_measurable
      X (-x) (a - x))
  have hcoe : Measurable (fun z : Ω × ℝ≥0 => (z.2 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp measurable_snd
  have hdown : Measurable (fun z : Ω × ℝ≥0 =>
      AvramDividend.Classical.twoSidedExitDownTime X (-x) z.1) :=
    hclocks.2.comp measurable_fst
  have hup : Measurable (fun z : Ω × ℝ≥0 =>
      AvramDividend.Classical.twoSidedExitUpTime X (a - x) z.1) :=
    hclocks.1.comp measurable_fst
  have hstate : Measurable (fun z : Ω × ℝ≥0 => x + X.X z.2 z.1) :=
    measurable_const.add
      ((AvramDividend.Classical.chat04_levy_joint_time_state_measurable X).comp
        (measurable_snd.prodMk measurable_fst))
  have hB : MeasurableSet B := by
    dsimp [B]
    exact (measurableSet_lt hcoe hdown).inter
      ((measurableSet_lt hcoe hup).inter (hstate hA))
  have hs : Measurable (fun t : ℝ≥0 =>
      P ((fun ω : Ω => (ω, t)) ⁻¹' B)) := by
    exact (p2m88_exp_clock_product_sections Ω P 1 zero_lt_one B hB).1
  have hsection :
      (fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted X.X x) 0 ω)
            (tauPlus (shifted X.X x) a ω) ∧
          shifted X.X x t ω ∈ A}) =
      fun t : ℝ≥0 => P ((fun ω : Ω => (ω, t)) ⁻¹' B) := by
    funext t
    apply measure_congr
    apply Filter.Eventually.of_forall
    intro ω
    change (((t : ℝ≥0∞) <
        min ((tauMinus (shifted X.X x) 0 ω : ℝ≥0∞))
          ((tauPlus (shifted X.X x) a ω : ℝ≥0∞)) ∧
        x + X.X t ω ∈ A) =
      ((t : ℝ≥0∞) < AvramDividend.Classical.twoSidedExitDownTime X (-x) ω ∧
        (t : ℝ≥0∞) < AvramDividend.Classical.twoSidedExitUpTime X (a - x) ω ∧
        x + X.X t ω ∈ A))
    erw [lt_min_iff, hlower ω, hupper ω, and_assoc]
  rw [hsection]
  exact hs
