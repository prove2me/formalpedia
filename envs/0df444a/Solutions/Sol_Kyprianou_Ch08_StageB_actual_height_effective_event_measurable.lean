-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_effective_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T05:39:18.062517+00:00
-- url     : https://prove2.me/submissions/07a88931-bcc2-45b3-bc32-f9edf9c6e8ca

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
import Theorems.Thm_stageB_ndd_iff_rat
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P 𝓕) (b h : ℝ) (hb : 0 < b) (hh : 0 < h) :
    MeasurableSet (setOf (fun ω : Ω =>
      twoSidedExitUpTime A b ω < ⊤ ∧
        NoDrawdownBeforeUpcrossing A.X b h ω)) := by
  classical
  let E : Set Ω := {ω | twoSidedExitUpTime A b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X b h ω}
  let U : Set Ω := ⋃ r : stageB_Bars h, {ω | stageB_bpay A (r : ℝ) b 0 ω ≠ 0}
  have hpay (r : stageB_Bars h) : Measurable (fun ω => stageB_bpay A (r : ℝ) b 0 ω) := by
    have hU := upperPassage_measurable_from_stopping A b
    have hB := barrierRuinTime_measurable A (r : ℝ)
    unfold stageB_bpay
    refine Measurable.ite (measurableSet_lt hU hB) ?_ measurable_const
    measurability
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact MeasurableSet.iUnion fun r => by
      have hEq : MeasurableSet {ω : Ω | stageB_bpay A (r : ℝ) b 0 ω = (0 : ℝ≥0∞)} :=
        measurableSet_eq_fun (hpay r) (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
      change MeasurableSet ({ω : Ω | stageB_bpay A (r : ℝ) b 0 ω = (0 : ℝ≥0∞)} : Set Ω)ᶜ
      exact hEq.compl
  have hEU : E = U := by
    ext ω
    constructor
    · intro hω
      have hfin : twoSidedExitUpTime A b ω ≠ ⊤ := ne_of_lt hω.1
      obtain ⟨r, hr⟩ := (stageB_ndd_iff_rat A b h hb hh ω hfin).mp hω.2
      exact mem_iUnion.2 ⟨r, hr⟩
    · intro hω
      rcases mem_iUnion.1 hω with ⟨r, hr⟩
      have hfin : twoSidedExitUpTime A b ω ≠ ⊤ := by
        intro htop
        have hz : stageB_bpay A (r : ℝ) b 0 ω = 0 := by
          simp [stageB_bpay, htop]
        exact hr hz
      exact ⟨lt_top_iff_ne_top.mpr hfin, (stageB_ndd_iff_rat A b h hb hh ω hfin).mpr ⟨r, hr⟩⟩
  change MeasurableSet E
  simpa [hEU] using hUmeas
