-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_filtered_restart_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:09:13.352015+00:00
-- url     : https://prove2.me/submissions/ec240c5b-b47d-4ae8-9e11-62729870674f

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_reward_representation
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_restart_split
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_fresh_reward
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_record_weight
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_real_avram_stopped_reward
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source record regeneration. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q x a l : ℝ), 0 ≤ q → 0 < a → 0 < x → x ≤ a → x < l →
      (∫ ω, if tauPlus X.X l ω < reflectedSupExit X.X x a ω
        then discountedAt q (tauPlus X.X l ω) else 0 ∂P) =
      upBeforeDownExpectation P X.X q (a-x) a *
      (∫ ω, if tauPlus X.X (l-x) ω < reflectedSupExit X.X 0 a ω
        then discountedAt q (tauPlus X.X (l-x) ω) else 0 ∂P) := by
  intro Ω mΩ P hP F X q x a l hq ha hx hxa hl
  obtain ⟨r,hr,hb,he⟩ := p2m810_shifted_reward_representation q a (l-x) hq
  let d := fun t : ℝ≥0 => Real.exp (-q*(t:ℝ))
  have hd : Measurable d := by unfold d; fun_prop
  have hdb (t : ℝ≥0) : 0 ≤ d t ∧ d t ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) t.2)⟩
  have h := (source_result81_uncapped_real_avram_stopped_reward X (x-a) x d hd hdb r hr hb).2
  have h1 := p2m810_filtered_record_weight Ω P F X q x a hq hx hxa
  have h2 (ω : Ω) := p2m810_filtered_restart_split Ω P F X q x a l hq ha hx hxa hl ω
  have h3 (ω : Ω) := p2m810_filtered_fresh_reward Ω P F X q a (l-x) ha (sub_pos.mpr hl) ω
  have hX0 (ω : Ω) : X.X 0 ω = 0 := X.X_zero ω
  have h4 (ω : Ω) : r (fun t => X.X t ω) =
      (if tauPlus X.X (l-x) ω < reflectedSupExit X.X 0 a ω
        then discountedAt q (tauPlus X.X (l-x) ω) else 0) := by
    have hh := he Ω P F X ω 0
    simpa [hX0 ω] using hh.trans (h3 ω)
  calc
    _ = ∫ ω, (if twoSidedExitUpTime X x ω < twoSidedExitDownTime X (x-a) ω
      then d (twoSidedExitUpTime X x ω).toNNReal *
        r (fun s => X.X ((twoSidedExitUpTime X x ω).toNNReal+s) ω -
          X.X (twoSidedExitUpTime X x ω).toNNReal ω) else 0) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      dsimp only [d]
      rw [h2 ω]
      simp only [← he Ω P F X ω ((twoSidedExitUpTime X x ω).toNNReal)]
    _ = _ := by
      simpa only [d,h1,show (fun ω => r (fun t => X.X t ω)) = _ from funext h4] using h
