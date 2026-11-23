-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_no_drawdown_null_measurable_of_effective_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T04:58:49.026474+00:00
-- url     : https://prove2.me/submissions/dceedbc9-e6f7-43d1-93a2-d3bfc1fc0f7b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Theorems.Thm_stageB_tauPlus_coe_eq
import Theorems.Thm_stageB_tauPlus_lt_iff
import Theorems.Thm_stageB_reflect_eq
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

private theorem stageB_no_drawdown_event_ae_eq_filtered_raw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P 𝓕) (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) (b h : ℝ) :
    {ω | NoDrawdownBeforeUpcrossing D.X b h ω} =ᵐ[P] {ω | NoDrawdownBeforeUpcrossing A.X b h ω} := by
  filter_upwards [hAX] with ω hω
  have ht : tauPlus A.X b ω = tauPlus D.X b ω := by simp [tauPlus, hω]
  have hr (t : ℝ≥0) : Kyprianou.Ch08.runningSup A.X t ω = Kyprianou.Ch08.runningSup D.X t ω := by
    simp [Kyprianou.Ch08.runningSup, hω]
  have href (t : ℝ≥0) : reflectAtSup A.X 0 t ω = reflectAtSup D.X 0 t ω := by
    simp [reflectAtSup, hr t, hω t]
  apply propext
  change (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < tauPlus D.X b ω → reflectAtSup D.X 0 t ω < h) ↔
    (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < tauPlus A.X b ω → reflectAtSup A.X 0 t ω < h)
  constructor
  · intro hD t htA
    simpa [href t] using hD t (by simpa [ht] using htA)
  · intro hA t htD
    simpa [href t] using hA t (by simpa [ht] using htD)

private theorem stageB_no_drawdown_eq_barrier_sup {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P 𝓕) (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (ω : Ω) :
    NoDrawdownBeforeUpcrossing A.X b h ω ↔ twoSidedExitUpTime A b ω ≤ ⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω := by
  constructor
  · intro hnd'
    change NoDrawdownBeforeUpcrossing A.X b h ω at hnd'
    change twoSidedExitUpTime A b ω ≤ ⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω
    by_contra hnot
    have hsup_lt : (⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω) <
        twoSidedExitUpTime A b ω := not_le.mp hnot
    obtain ⟨w, hsupw, hwtau⟩ := exists_between hsup_lt
    let u : ℝ≥0 := w.toNNReal
    have hwu : (u : ℝ≥0∞) = w := ENNReal.coe_toNNReal (ne_top_of_lt (lt_of_lt_of_le hwtau le_top))
    have hu_tau : (u : WithTop ℝ≥0) < tauPlus A.X b ω :=
      (stageB_tauPlus_lt_iff A b ω (t := u)).2 (by simpa [hwu] using hwtau)
    obtain ⟨v, hvI, hvmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
      (⟨0, ⟨le_rfl, bot_le⟩⟩ : (Icc (0 : ℝ≥0) u).Nonempty) isCompact_Icc
      (reflectedSup_upperSemicontinuousOn_Icc A ω u)
    have hv_tau : (v : WithTop ℝ≥0) < tauPlus A.X b ω := lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hvI.2) hu_tau
    have hvh : reflectedSup A v ω < h := by
      simpa only [stageB_reflect_eq A v ω] using hnd' v hv_tau
    obtain ⟨q, hqM, hqh⟩ := exists_rat_btwn (max_lt hh hvh)
    let r : stageB_Bars h := ⟨q, lt_of_le_of_lt (le_max_left _ _) hqM, hqh⟩
    have hMr : reflectedSup A v ω < (r : ℝ) := lt_of_le_of_lt (le_max_right _ _) hqM
    have hru : (u : ℝ≥0∞) ≤ barrierRuinTime A (r : ℝ) ω := by
      unfold barrierRuinTime drawdown
      refine le_iInf fun t => le_iInf fun ht => ?_
      have htu : ¬ t < u := by
        intro htu
        have htI : t ∈ Icc (0 : ℝ≥0) u := ⟨bot_le, le_of_lt htu⟩
        have hleM : reflectedSup A t ω ≤ reflectedSup A v ω := hvmax htI
        have hrt : (r : ℝ) < reflectedSup A t ω := ht
        exact (not_lt_of_ge (le_of_lt hMr)) (lt_of_lt_of_le hrt hleM)
      exact ENNReal.coe_le_coe.mpr (le_of_not_gt htu)
    have hleSup : barrierRuinTime A (r : ℝ) ω ≤
        ⨆ s : stageB_Bars h, barrierRuinTime A (s : ℝ) ω :=
      le_iSup (fun s : stageB_Bars h => barrierRuinTime A (s : ℝ) ω) r
    have huw : w ≤ (⨆ s : stageB_Bars h, barrierRuinTime A (s : ℝ) ω) := by
      simpa [← hwu] using hru.trans hleSup
    exact (not_le_of_gt hsupw) huw
  · intro htauSup
    change NoDrawdownBeforeUpcrossing A.X b h ω
    change twoSidedExitUpTime A b ω ≤
      ⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω at htauSup
    intro t ht
    have htENN : (t : ℝ≥0∞) < twoSidedExitUpTime A b ω :=
      (stageB_tauPlus_lt_iff A b ω (t := t)).1 ht
    by_contra hnot
    have hdh : h ≤ reflectedSup A t ω := by
      have := le_of_not_gt hnot
      simpa only [stageB_reflect_eq A t ω] using this
    have hru (r : stageB_Bars h) :
        barrierRuinTime A (r : ℝ) ω ≤ (t : ℝ≥0∞) := by
      unfold barrierRuinTime drawdown
      have hrt : (r : ℝ) < reflectedSup A t ω := lt_of_lt_of_le r.2.2 hdh
      exact (iInf_le (fun s : ℝ≥0 => ⨅ _ : (r : ℝ) < reflectedSup A s ω, (s : ℝ≥0∞)) t).trans
        (iInf_le (fun _ : (r : ℝ) < reflectedSup A t ω => (t : ℝ≥0∞)) hrt)
    have hsup_le : (⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω) ≤
        (t : ℝ≥0∞) := iSup_le hru
    exact (not_lt_of_ge (htauSup.trans hsup_le)) htENN
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P 𝓕) (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (hE : MeasurableSet {ω : Ω | twoSidedExitUpTime A b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X b h ω}) :
    NullMeasurableSet {ω : Ω | NoDrawdownBeforeUpcrossing D.X b h ω} P := by
  classical
  let N : Set Ω := {ω | NoDrawdownBeforeUpcrossing A.X b h ω}
  let R : Set Ω := {ω | twoSidedExitUpTime A b ω ≤ ⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω}
  have hNR : N = R := by
    ext ω
    change NoDrawdownBeforeUpcrossing A.X b h ω ↔
      twoSidedExitUpTime A b ω ≤ ⨆ r : stageB_Bars h, barrierRuinTime A (r : ℝ) ω
    exact stageB_no_drawdown_eq_barrier_sup A b h hb hh ω
  have hRmeas : MeasurableSet R := by
    dsimp [R]
    exact measurableSet_le (upperPassage_measurable_from_stopping A b)
      (Measurable.iSup fun r : stageB_Bars h => barrierRuinTime_measurable A (r : ℝ))
  have hNA : NullMeasurableSet N P := by
    rw [hNR]
    exact hRmeas.nullMeasurableSet
  exact hNA.congr (stageB_no_drawdown_event_ae_eq_filtered_raw A D hAX b h).symm
