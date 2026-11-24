-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.p2m87_qpos_two_sided_occupation_sections_measurable_for_bridge
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T04:41:23.013208+00:00
-- url     : https://prove2.me/submissions/5ae235f8-3d72-4a8e-8940-39f83aba4e19

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_upper_shifted_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_source_lower_clock_eq
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ (A : Set ℝ), MeasurableSet A →
      Measurable (fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted D.X x) 0 ω)
            (tauPlus (shifted D.X x) a ω) ∧
          shifted D.X x t ω ∈ A}) := by
  intro Ω mΩ P _ D ψ hψ a x ha hx hxa A hA
  -- pass to the filtered Avram model with almost surely identical paths
  obtain ⟨F, Y, hXY, -⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  -- the jointly measurable time-state event for the Avram model
  let S : Set (ℝ≥0 × Ω) :=
    {z | ((z.1 : ℝ≥0∞) <
        min (AvramDividend.Classical.twoSidedExitDownTime Y (-x) z.2)
          (AvramDividend.Classical.twoSidedExitUpTime Y (a - x) z.2)) ∧
      x + Y.X z.1 z.2 ∈ A}
  have hS : MeasurableSet S := by
    obtain ⟨hup, hdown⟩ :=
      AvramDividend.Classical.chat03_both_named_passage_clocks_measurable Y (-x) (a - x)
    have hj := AvramDividend.Classical.chat04_levy_joint_time_state_measurable Y
    have hf : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp measurable_fst
    have hg : Measurable (fun z : ℝ≥0 × Ω =>
        min (AvramDividend.Classical.twoSidedExitDownTime Y (-x) z.2)
          (AvramDividend.Classical.twoSidedExitUpTime Y (a - x) z.2)) :=
      (hdown.comp measurable_snd).min (hup.comp measurable_snd)
    have h1 : MeasurableSet {z : ℝ≥0 × Ω | (z.1 : ℝ≥0∞) <
        min (AvramDividend.Classical.twoSidedExitDownTime Y (-x) z.2)
          (AvramDividend.Classical.twoSidedExitUpTime Y (a - x) z.2)} :=
      measurableSet_lt hf hg
    have h2 : MeasurableSet {z : ℝ≥0 × Ω | x + Y.X z.1 z.2 ∈ A} :=
      (measurable_const.add hj) hA
    exact h1.inter h2
  have hmeas : Measurable (fun t : ℝ≥0 => P (Prod.mk t ⁻¹' S)) :=
    measurable_measure_prodMk_left hS
  convert hmeas using 1
  funext t
  apply measure_congr
  filter_upwards [hXY] with ω hω
  have hpath : shifted D.X x = fun u ω' => x + D.X u ω' := rfl
  have hdown : tauMinus (shifted D.X x) 0 ω = tauMinus (shifted Y.X x) 0 ω := by
    simp only [tauMinus, shifted, hω]
  have hup : tauPlus (shifted D.X x) a ω = tauPlus (shifted Y.X x) a ω := by
    simp only [tauPlus, shifted, hω]
  have hdown' := p2m88_avram_source_lower_clock_eq Ω P F Y x ω
  have hup' := qzero_avram_upper_shifted_clock_eq Ω P F Y a x ha hx hxa ω
  apply propext
  change ((t : WithTop ℝ≥0) <
      min (tauMinus (shifted D.X x) 0 ω) (tauPlus (shifted D.X x) a ω) ∧
      shifted D.X x t ω ∈ A) ↔
    ((t : ℝ≥0∞) <
        min (AvramDividend.Classical.twoSidedExitDownTime Y (-x) ω)
          (AvramDividend.Classical.twoSidedExitUpTime Y (a - x) ω) ∧
      x + Y.X t ω ∈ A)
  rw [hdown, hup, ← hdown', ← hup', hpath]
  simp only [hω]
  rfl
