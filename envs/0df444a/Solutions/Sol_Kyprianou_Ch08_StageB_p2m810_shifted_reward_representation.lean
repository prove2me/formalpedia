-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_shifted_reward_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:08:58.052752+00:00
-- url     : https://prove2.me/submissions/cd56e942-c3b2-467d-9e03-a69c6cc00e9f

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sampled_upper_clock_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sampled_drawdown_clock_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source record regeneration. -/
theorem solution :
    ∀ (q a c : ℝ), 0 ≤ q →
      ∃ r : (ℝ≥0 → ℝ) → ℝ, Measurable r ∧
        (∀ f, 0 ≤ r f ∧ r f ≤ 1) ∧
        (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
          (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F)
          (ω : Ω) (u : ℝ≥0),
          r (fun t => X.X (u+t) ω-X.X u ω) =
          (let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
      let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
      let R : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - sSup (f '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)
      if U < R then discountedAt q U else 0)) := by
  intro q a c hq
  obtain ⟨hd,hb,_⟩ := source_result81_measurable_ruin_path_reward q a hq
  let s : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
    (((((Nat.unpair j).1+1):ℕ):ℝ≥0)⁻¹)
  let U := fun f : ℝ≥0 → ℝ => ⨅ i : ℕ, if c < f (s i) then (s i:ℝ≥0∞) else ⊤
  let R := fun f : ℝ≥0 → ℝ => ⨅ i : ℕ, if f (s i) -
    (⨆ j : ℕ, if s j ≤ s i then ENNReal.ofReal (f (s j)) else 0).toReal < -a
    then (s i:ℝ≥0∞) else ⊤
  have hU : Measurable U := p2m810_sampled_upper_clock_measurable s c
  have hR : Measurable R := p2m810_sampled_drawdown_clock_measurable s a
  refine ⟨fun f => if U f < R f then discountedAt q (U f) else 0,
    Measurable.ite (measurableSet_lt hU hR) (hd.comp hU) measurable_const, ?_, ?_⟩
  · intro f
    dsimp only
    split
    · exact hb _
    · exact ⟨le_rfl,zero_le_one⟩
  · intro Ω mΩ P F X ω u
    let f : ℝ≥0 → ℝ := fun t => X.X (u+t) ω-X.X u ω
    have h := avram_wave3_01_true_shifted_record_ruin_clock_pair X ω u a c
    exact congrArg (fun p : ℝ≥0∞ × ℝ≥0∞ =>
      if p.1 < p.2 then discountedAt q p.1 else 0) h.symm
